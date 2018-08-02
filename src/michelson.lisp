(include-book "acl2s/defunc" :dir :system)
(include-book "acl2s/ccg/ccg" :ttags ((:ccg)) :dir :system :load-compiled-file nil)
(ld "acl2s/ccg/ccg-settings.lsp" :dir :system)

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


(defmacro gen-reified-typep (types type-expr value-expr)
  (if (endp types)
      `(and (mlist-typep ,type-expr)
            (mlist-datap ,value-expr)
            (or (endp ,value-expr)
                (and (reified-typep (mlist-type-type ,type-expr)
                                    (car ,value-expr))
                     (reified-typep ,type-expr (cdr ,value-expr)))))
    (let* ((type-info (car types))
           (type (first type-info))
           (pred (third type-info)))
      `(or (and (equal (quote ,type) ,type-expr)
                (,pred ,value-expr))
           (gen-reified-typep ,(cdr types) ,type-expr ,value-expr)))))

(defmacro register-mtypes (type-preds)
  `(progn
     (defdata mbase-type (oneof ,@(quote* (nth-lol 0 type-preds))))
     (defdata (mtype (oneof mbase-type mlist-type))
       (mlist-type (cons 'LIST mtype)))
     (defdata mbase-data (oneof ,@(nth-lol 1 type-preds)))
     (defdata (mdata (oneof mlist-data ,@(nth-lol 1 type-preds)))
       (mlist-data (list mdata)))
     (defunc mlist-type-type (lt)
       :input-contract (mlist-typep lt)
       :output-contract (mtypep (mlist-type-type lt))
       (cdr lt))
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

;; Quickly switch between test? and defthm
(defmacro defthm? (name thm)
  (declare (ignorable name))
  `(test? ,thm))
(defunc make-instr-pred (instr)
  :input-contract (symbolp instr)
  :output-contract (symbolp (make-instr-pred instr))
  (intern-in-package-of-symbol
   (string-append "INSTR-"
                  (string-append (string instr)
                                 "P"))
   'instr))


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
(defdata-disjoint symbolic-stack typerror)

(defdata failgas 'failgas)
(defdata fail-message (cons 'fail string))
(defdata fail-raw 'fail)
(defdata fail (oneof fail-message fail-raw))

(defdata gas integer)

(defdata gas-cost integer)

(defdata interp-success (cons stack gas))
(defdata interp-failure (oneof fail failgas))
(defdata-disjoint interp-success interp-failure)

(defdata interp-result (oneof interp-success interp-failure typerror))

(defunc isuccess (stack gas)
  :input-contract (and (stackp stack) (gasp gas))
  :output-contract (interp-successp (isuccess stack gas))
  (cons stack gas))

(defunc success-stack (success)
  :input-contract (interp-successp success)
  :output-contract (stackp (success-stack success))
  (car success))

(defunc success-gas (success)
  :input-contract (interp-successp success)
  :output-contract (gasp (success-gas success))
  (cdr success))

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

(defunc out-of-gasp (gas)
  :input-contract (gasp gas)
  :output-contract (booleanp (out-of-gasp gas))
  (<= gas 0))

(defmacro gen-interpreter-step (primops instr-expr stack gas-expr)
  (if (endp primops)
      (quote 'typerror)
    (let* ((instr-info (car primops))
           (input-stack-types (car (second instr-info)))
           (instr-pred (make-instr-pred (car instr-info)))
           (function (third instr-info))
           (gas-func (fourth instr-info))
           (accessor-ind (- (length input-stack-types) 1))
           (top-accessors (list-accessors input-stack-types stack)))
      `(if (and (,instr-pred ,instr-expr)
                (,(nth accessor-ind *STACK-PREDS*) ,stack)
                ,(gen-check-types input-stack-types *LIST-ACCESSORS* stack))
           (let ((remaining-gas (consume-gas ,gas-expr (,gas-func ,@top-accessors))))
             (if (out-of-gasp remaining-gas)
                 'failgas
               (isuccess
                (cons (,function ,@top-accessors)
                      (,(nth accessor-ind *LIST-REMAINDERS*) ,stack))
                remaining-gas)))
         (gen-interpreter-step ,(cdr primops)
                               ,instr-expr
                               ,stack
                               ,gas-expr)))))

(defmacro primops (ops)
  `(progn
     (declare-primops ,ops nil)
     (defunc typechecker-step (instr stack)
       :input-contract (and (primopp instr) (symbolic-stackp stack))
       :output-contract (tc-resultp (typechecker-step instr stack))
       (gen-typechecker-step ,ops instr stack))
     (defunc interpreter-step (instr stack gas)
       :input-contract (and (primopp instr) (stackp stack) (gasp gas))
       :output-contract (interp-resultp (interpreter-step instr stack gas))
       (if (out-of-gasp gas)
           'failgas
           (gen-interpreter-step ,ops instr stack gas)))))

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

(defunc consume-gas (gas cost)
    :input-contract (and (gas-costp cost) (gasp gas))
    :output-contract (gasp (consume-gas gas cost))
    (- gas cost))

;; TODO: find better solution to unused parameters
(progn
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (defunc preliminary-gas-unop (x)
    :input-contract t
    :output-contract (gas-costp (preliminary-gas-unop x))
    1)

  (defunc preliminary-gas-binop (x1 x2)
    :input-contract t
    :output-contract (gas-costp (preliminary-gas-binop x1 x2))
    1)

  (set-ignore-ok nil)
  (set-irrelevant-formals-ok nil))

(primops
 ((add ((int int) . (int)) + preliminary-gas-binop)
  (sub ((int int) . (int)) - preliminary-gas-binop)
  (mul ((int int) . (int)) * preliminary-gas-binop)

  (and ((bool bool) . (bool)) and preliminary-gas-binop)
  (or ((bool bool) . (bool)) or preliminary-gas-binop)

  (cmp ((int int) . (int)) cmp-int preliminary-gas-binop)
  (eq  ((int) . (bool)) cmpres-eq preliminary-gas-unop)))

(defthm typechecker-step-progress
  (implies (and (symbolic-stackp sym-stack)
                (stackp stack)
                (primopp op)
                (reified-stackp sym-stack stack)
                (gasp gas)
                (not (typerrorp (typechecker-step op sym-stack))))
           (let ((stepped (interpreter-step op stack gas)))
             (or (failgasp stepped)
                 (and (not (typerrorp stepped))
                      (reified-stackp (typechecker-step op sym-stack)
                                      (success-stack stepped)))))))
(defthm step-decreases-gas
  (implies (and (stackp stack)
                (primopp op)
                (gasp gas)
                (interp-successp (interpreter-step op stack gas)))
           (< (success-gas (interpreter-step op stack gas)) gas)))

(defdata
  (instr (oneof primop instr-dip instr-if))
  (instr-dip (cons 'DIP instr-seq))
  (instr-if (list 'IF instr-seq instr-seq))
  (instr-seq (listof instr)))

(defdata-disjoint instr-dip instr-if)
(defdata-disjoint primop instr-if)

(defunc instr-if-conseq (instr)
  :input-contract (instr-ifp instr)
  :output-contract (instr-seqp (instr-if-conseq instr))
  (second instr))

(defunc instr-if-alt (instr)
  :input-contract (instr-ifp instr)
  :output-contract (instr-seqp (instr-if-alt instr))
  (third instr))

(defunc instr-dip-instrs (instr)
  :input-contract (instr-dipp instr)
  :output-contract (instr-seqp (instr-dip-instrs instr))
  (cdr instr))

(in-theory (disable stackp
                    gasp
                    instr-seqp
                    instr-dipp
                    instr-ifp
                    primopp
                    tc-resultp
                    typerrorp
                    out-of-gasp
                    symbolic-stackp
                    ))

(defunc typecheck (instrs stack)
  :input-contract (and (instr-seqp instrs) (symbolic-stackp stack))
  :output-contract (tc-resultp (typecheck instrs stack))
  (cond ((endp instrs) stack)
        ((primopp (car instrs))
         (let ((stepped (typechecker-step (car instrs) stack)))
           (if (typerrorp stepped)
               stepped
             (typecheck (cdr instrs) stepped))))
        ((and (instr-ifp (car instrs)) (consp stack) (equal 'bool (car instrs)))
         (let* ((instr (car instrs))
                (branch-stack (cdr stack))
                (conseq-stepped (typecheck (instr-if-conseq instr) branch-stack))
                (alt-stepped (typecheck (instr-if-alt instr) branch-stack)))
           (if (and (symbolic-stackp conseq-stepped)
                    (symbolic-stackp alt-stepped)
                    (equal conseq-stepped alt-stepped))
               (typecheck (cdr instrs) conseq-stepped)
             'typerror)))
        ((and (instr-dipp (car instrs)) (consp stack))
         (let* ((first-stack (car stack))
                (rest-stack (cdr stack))
                (stepped (typecheck (instr-dip-instrs (car instrs)) rest-stack)))
           (if (symbolic-stackp stepped)
               (typecheck (cdr instrs) (cons first-stack stepped))
             'typerror)))
        (t 'typerror)))

(defunc interp (instrs stack gas)
  :input-contract (and (instr-seqp instrs) (stackp stack) (gasp gas))
  :output-contract (interp-resultp (interp instrs stack gas))
  (cond ((out-of-gasp gas) 'failgas)
        ((endp instrs) (isuccess stack gas))
        ((primopp (car instrs))
         (let ((stepped (interpreter-step (car instrs) stack gas)))
           (if (interp-successp stepped)
               (interp (cdr instrs) (success-stack stepped) (success-gas stepped))
             stepped)))
        ((and (instr-ifp (car instrs))
              (consp stack)
              (booleanp (car instrs)))
         (let* ((instr (car instrs))
                (branch-stack (cdr stack))
                (stepped (interp (if (car stack)
                                     (instr-if-conseq instr)
                                     (instr-if-alt instr))
                                 branch-stack
                                 gas)))
           (if (interp-successp stepped)
               (interp (cdr instrs) (success-stack stepped) (success-gas stepped))
             stepped)))
        ((and (instr-dipp (car instrs)) (consp stack))
         (let* ((first-stack (car stack))
                (rest-stack (cdr stack))
                (stepped (interp (instr-dip-instrs (car instrs)) rest-stack gas)))
           (if (interp-successp stepped)
               (interp (cdr instrs)
                       (cons first-stack (success-stack stepped))
                       (success-gas stepped))
             stepped)))
        (t 'typerror)))
