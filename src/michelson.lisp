(include-book "acl2s/defunc" :dir :system)

(in-package "ACL2S")

(defun nth-lol (n lol)
  (if (endp lol)
      nil
    (cons (nth n (car lol)) (nth-lol n (cdr lol)))))

(defun quote* (l)
  (if (endp l)
      nil
    (cons (list 'quote (car l)) (quote* (cdr l)))))

(defunc prefix-sym (pref s)
  :input-contract (and (symbolp pref) (symbolp s))
  :output-contract (symbolp (prefix-sym pref s))
  (intern-in-package-of-symbol
   (concatenate 'acl2::string
                (symbol-name pref)
                "-"
                (symbol-name s))
   s))


(defunc make-instr-pred (instr)
  :input-contract (symbolp instr)
  :output-contract (symbolp (make-instr-pred instr))
  (intern-in-package-of-symbol
   (string-append "INSTR-"
                  (string-append (string instr)
                                 "P"))
   'instr))

(defmacro gen-reified-typep (types type-expr value-expr)
  (if (endp types)
      nil
    (let* ((type-info (car types))
           (type (first type-info))
           (pred (third type-info)))
      `(or (and (equal (quote ,type) ,type-expr)
                (,pred ,value-expr))
           (gen-reified-typep ,(cdr types) ,type-expr ,value-expr)))))

(defmacro register-mtypes (type-preds)
  `(progn
     (defdata mtype (oneof ,@(quote* (nth-lol 0 type-preds))))
     (defdata mdata (oneof ,@(nth-lol 1 type-preds)))
     (defunc reified-typep (type value)
       :input-contract (and (mtypep type) (mdatap value))
       :output-contract (booleanp (reified-typep type value))
       (gen-reified-typep ,type-preds type value))
     ;; Used to get predicates in other macros
     (defconst *PRED-LOOKUP*
       (pairlis$ (quote ,(nth-lol 0 type-preds))
                 (quote ,(nth-lol 2 type-preds))))))
(register-mtypes
 ((int integer integerp)
  (string string stringp)
  (bool boolean booleanp)))

(defdata symbolic-stack (listof mtype))
(defdata stack (listof mdata))

(defunc reified-stackp (sym stack)
  :input-contract (and (symbolic-stackp sym) (stackp stack))
  :output-contract (booleanp (reified-stackp sym stack))
  (cond ((and (consp sym) (consp stack))
         (and (reified-typep (car sym) (car stack))
              (reified-stackp (cdr sym) (cdr stack))))
        ((endp sym) (endp stack))
        (t nil)))


(defmacro declare-primops (primops instrs)
  (if (endp primops)
      `(defdata primop (oneof ,@instrs))
    (let* ((instr (caar primops))
           (prefixed (prefix-sym 'instr instr)))
      `(progn
         (defdata ,prefixed (quote ,instr))
         (declare-primops ,(cdr primops) ,(cons prefixed instrs))))))

(defdata typerror 'typerror)
(defdata tc-result (oneof symbolic-stack typerror))

(defdata failgas 'failgas)
(defdata fail-no-message (cons 'fail string))
(defdata fail-raw 'fail)
(defdata fail (oneof fail-no-message fail-raw))

(defdata interp-result (oneof stack fail failgas typerror))

(defunc transform-sym-stack (checking-stack current-stack output-stack)
  :input-contract (and (symbolic-stackp checking-stack)
                       (symbolic-stackp current-stack)
                       (symbolic-stackp output-stack))
  :output-contract (tc-resultp (transform-sym-stack checking-stack
                                                    current-stack
                                                    output-stack))
  (cond ((endp checking-stack) (append output-stack current-stack))
        ((and (consp current-stack)
              (equal (car checking-stack) (car current-stack)))
         (transform-sym-stack (cdr checking-stack)
                              (cdr current-stack)
                              output-stack))
        (t 'typerror)))

(defmacro gen-typechecker-step (primops instr-expr test-stack)
  (if (endp primops)
      (quote 'typerror)
    (let* ((instr-info (car primops))
           (stack-types (second instr-info))
           (instr-pred (make-instr-pred (car instr-info))))
      `(if (,instr-pred ,instr-expr)
           (transform-sym-stack (quote ,(car stack-types))
                                ,test-stack
                                (quote ,(cdr stack-types)))
         (gen-typechecker-step ,(cdr primops)
                               ,instr-expr
                               ,test-stack)))))

(defconst *LIST-ACCESSORS*
  '(FIRST SECOND THIRD FOURTH FIFTH SIXTH SEVENTH EIGHTH NINTH TENTH))
(defconst *LIST-REMAINDERS*
  '(CDR CDDR CDDDR CDDDDR CDDDDDR CDDDDDDR CDDDDDDR CDDDDDDDR CDDDDDDDR CDDDDDDDDR))

(defdata unary-op-stack
  (cons mdata stack))
(defdata binary-op-stack
  (cons mdata (cons mdata stack)))
(defdata ternary-op-stack
  (cons mdata (cons mdata (cons mdata stack))))
(defdata quaternary-op-stack
  (cons mdata (cons mdata (cons mdata (cons mdata stack)))))
(defdata quernary-op-stack
  (cons mdata (cons mdata (cons mdata (cons mdata (cons mdata stack))))))

(defdata-subtype unary-op-stack stack)
(defdata-subtype binary-op-stack unary-op-stack)
(defdata-subtype ternary-op-stack binary-op-stack)
(defdata-subtype quaternary-op-stack ternary-op-stack)
(defdata-subtype quernary-op-stack quaternary-op-stack)

(defconst *STACK-PREDS*
  '(unary-op-stackp
    binary-op-stackp
    ternary-op-stackp
    quaternary-op-stackp
    quernary-op-stack))

(defun list-accessors-help (elements accessors test-expr)
  (if (endp elements)
      nil
    (cons `(,(car accessors) ,test-expr)
          (list-accessors-help (cdr elements) (cdr accessors) test-expr))))

(defun list-accessors (elements test-expr)
  (list-accessors-help elements *LIST-ACCESSORS* test-expr))

(defun gen-check-types (types accessors stack-expr)
  (if (endp types)
      't
    `(and (,(cdr (assoc (car types) *PRED-LOOKUP*))
           (,(car accessors) ,stack-expr))
          ,(gen-check-types (cdr types) (cdr accessors) stack-expr))))

(defmacro gen-interpreter-step (primops instr-expr stack)
  (if (endp primops)
      (quote 'typerror)
    (let* ((instr-info (car primops))
           (input-stack-types (car (second instr-info)))
           (instr-pred (make-instr-pred (car instr-info)))
           (function (third instr-info))
           (accessor-ind (- (length input-stack-types) 1)))
      `(if (and (,instr-pred ,instr-expr)
                (,(nth accessor-ind *STACK-PREDS*) ,stack)
                ,(gen-check-types input-stack-types *LIST-ACCESSORS* stack))
           (cons (,function ,@(list-accessors input-stack-types stack))
                 (,(nth accessor-ind *LIST-REMAINDERS*) ,stack))
         (gen-interpreter-step ,(cdr primops)
                               ,instr-expr
                               ,stack)))))

(defmacro primops (ops)
  `(progn
     (declare-primops ,ops nil)
     (defunc typechecker-step (instr stack)
       :input-contract (and (primopp instr) (symbolic-stackp stack))
       :output-contract (tc-resultp (typechecker-step instr stack))
       (gen-typechecker-step ,ops instr stack))
     (defunc interpreter-step (instr stack)
       :input-contract (and (primopp instr) (stackp stack))
       :output-contract (interp-resultp (interpreter-step instr stack))
       (gen-interpreter-step ,ops instr stack))))

(defunc cmp-int (n1 n2)
  :input-contract (and (integerp n1) (integerp n2))
  :output-contract (integerp (cmp-int n1 n2))
  (cond ((> n1 n2) 1)
        ((= n1 n2) 0)
        (t -1)))

(defunc cmpres-eq (c)
  :input-contract (integerp c)
  :output-contract (booleanp (cmpres-eq c))
  (= c 0))

(primops
 ((add ((int int) . (int)) +)
  (sub ((int int) . (int)) -)
  (mul ((int int) . (int)) *)

  (and ((bool bool) . (bool)) and)
  (or ((bool bool) . (bool)) or)

  (cmp ((int int) . (int)) cmp-int)
  (eq  ((int) . (bool)) cmpres-eq)))

(defthm typechecker-step-progress
  (implies (and (symbolic-stackp sym-stack)
                (stackp stack)
                (primopp op)
                (reified-stackp sym-stack stack)
                (not (typerrorp (typechecker-step op sym-stack))))
           (and (reified-stackp (typechecker-step op sym-stack)
                                (interpreter-step op stack))
                (not (typerrorp (interpreter-step op stack))))))
