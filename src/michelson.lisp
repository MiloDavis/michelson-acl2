(include-book "acl2s/defunc" :dir :system)
(include-book "acl2s/ccg/ccg" :ttags ((:ccg)) :dir :system)
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

(defunc make-predicate (s)
  :input-contract (symbolp s)
  :output-contract (symbolp (make-predicate s))
  (intern-in-package-of-symbol
   (concatenate 'acl2::string
                (symbol-name s)
                "P")
   s))

(defconst *LIST-ACCESSORS*
  '(FIRST SECOND THIRD FOURTH FIFTH SIXTH SEVENTH EIGHTH NINTH TENTH))
(defconst *LIST-REMAINDERS*
  '(CDR CDDR CDDDR CDDDDR CDDDDDR CDDDDDDR CDDDDDDR CDDDDDDDR CDDDDDDDR CDDDDDDDDR))

;; Quickly switch between test? and defthm
(defmacro defthm? (name thm &rest rest)
  (declare (ignorable name rest))
  `(test? ,thm))

(defmacro stack-preds (ending data-name stack)
  `(progn
     (defdata ,(prefix-sym 'unary-op ending) (cons ,data-name ,stack))
     (defdata ,(prefix-sym 'binary-op ending)
       (cons ,data-name (cons ,data-name ,stack)))
     (defdata ,(prefix-sym 'ternary-op ending)
       (cons ,data-name (cons ,data-name (cons ,data-name ,stack))))
     (defdata ,(prefix-sym 'quaternary-op ending)
       (cons ,data-name
             (cons ,data-name
                   (cons ,data-name
                         (cons ,data-name ,stack)))))
     (defdata ,(prefix-sym 'quernary-op ending)
       (cons ,data-name
             (cons ,data-name
                   (cons ,data-name
                         (cons ,data-name
                               (cons ,data-name ,stack))))))

     (defdata-subtype ,(prefix-sym 'unary-op ending) ,stack)
     (defdata-subtype ,(prefix-sym 'binary-op ending)
       ,(prefix-sym 'unary-op ending))
     (defdata-subtype ,(prefix-sym 'ternary-op ending)
       ,(prefix-sym 'binary-op ending))
     (defdata-subtype ,(prefix-sym 'quaternary-op ending)
       ,(prefix-sym 'ternary-op ending))
     (defdata-subtype ,(prefix-sym 'quernary-op ending)
       ,(prefix-sym 'quaternary-op ending))
     (defconst ,(intern-in-package-of-symbol
                 (concatenate 'acl2::string
                              "*"
                              (symbol-name ending)
                              "-PREDS*")
                 ending)
       '(,(make-predicate (prefix-sym 'unary-op ending))
         ,(make-predicate (prefix-sym 'binary-op ending))
         ,(make-predicate (prefix-sym 'ternary-op ending))
         ,(make-predicate (prefix-sym 'quaternary-op ending))
         ,(make-predicate (prefix-sym 'quernary-op ending))))))

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
     (defdata symbolic-stack (listof mtype))
     (defdata stack (listof mdata))
     (stack-preds sym-stack mtype symbolic-stack)
     (stack-preds stack mdata stack)
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


(defunc reified-stackp (sym stack)
  :input-contract (and (symbolic-stackp sym) (stackp stack))
  :output-contract (booleanp (reified-stackp sym stack))
  (cond ((and (consp sym) (consp stack))
         (and (reified-typep (car sym) (car stack))
              (reified-stackp (cdr sym) (cdr stack))))
        ((endp sym) (endp stack))
        (t nil)))

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

(defun list-accessors-help (elements accessors test-expr)
  (if (endp elements)
      nil
    (cons `(,(car accessors) ,test-expr)
          (list-accessors-help (cdr elements) (cdr accessors) test-expr))))

(defun list-accessors (elements test-expr)
  (list-accessors-help elements *LIST-ACCESSORS* test-expr))

(defun gen-check-symbolic-types (types accessors stack-expr)
  (if (endp types)
      't
    `(and (equal (quote ,(car types))
                 (,(car accessors) ,stack-expr))
          ,(gen-check-symbolic-types (cdr types) (cdr accessors) stack-expr))))

(defmacro gen-typechecker-step (primops instr-expr test-stack)
  (if (endp primops)
      (quote 'typerror)
    (let* ((instr-info (car primops))
           (stack-types (second instr-info))
           (instr-pred (make-instr-pred (car instr-info)))
           (rest-accessor-index (1- (len (car stack-types)))))
      `(if (,instr-pred ,instr-expr)
           (if (and (,(nth rest-accessor-index *SYM-STACK-PREDS*)
                     ,test-stack)
                    ,(gen-check-symbolic-types (car stack-types)
                                               *LIST-ACCESSORS*
                                               test-stack))
               (list* ,@(quote* (cdr stack-types))
                      (,(nth rest-accessor-index *LIST-REMAINDERS*)
                       ,test-stack))
             'typerror)
         (gen-typechecker-step ,(cdr primops)
                               ,instr-expr
                               ,test-stack)))))

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

(defthm stack-reified-selectors
  (implies (and (symbolic-stackp sym-stack)
                (stackp stack)
                (reified-stackp sym-stack stack))
           (and (iff (unary-op-sym-stackp sym-stack)
                     (unary-op-stackp stack))
                (iff (binary-op-sym-stackp sym-stack)
                     (binary-op-stackp stack))
                (iff (ternary-op-sym-stackp sym-stack)
                     (ternary-op-stackp stack))
                (iff (quaternary-op-sym-stackp sym-stack)
                     (quaternary-op-stackp stack))
                (iff (quernary-op-sym-stackp sym-stack)
                     (quernary-op-stackp stack))
                ))
  :hints (("Goal" :in-theory (disable (:DEFINITION MBASE-TYPEP)
                                      (:DEFINITION MDATAP)
                                      (:DEFINITION MLIST-DATAP)
                                      (:DEFINITION MTYPEP)
                                      (:DEFINITION MLIST-TYPEP)
                                      ))))

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

(defmacro with-disable (disabled-list &rest exprs)
  `(progn
    (in-theory (disable ,@disabled-list))
    ,@exprs
    (in-theory (enable ,@disabled-list))))

(with-disable
 ((:DEFINITION CMP-INT-DEFINITION-RULE)
  primopp
  gasp
  (:DEFINITION MDATAP)
  (:DEFINITION MTYPEP)
  (:DEFINITION MLIST-TYPEP)
  (:DEFINITION OUT-OF-GASP-DEFINITION-RULE)
  (:DEFINITION FIX)
  )

 (defthm typechecker-step-typerror
   (implies (and (symbolic-stackp sym-stack)
                 (stackp stack)
                 (primopp op)
                 (reified-stackp sym-stack stack)
                 (gasp gas)
                 (not (failgasp (interpreter-step op stack gas))))
            (iff (typerrorp (typechecker-step op sym-stack))
                 (typerrorp (interpreter-step op stack gas))))))

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

(with-disable
 (
  stackp
  gasp
  instr-seqp
  instr-dipp
  instr-ifp
  instr-if=>def
  instr-dip=>def
  primopp
  tc-resultp
  typerrorp
  out-of-gasp
  symbolic-stackp
  )

 (defunc typecheck (instrs stack)
   :input-contract (and (instr-seqp instrs) (symbolic-stackp stack))
   :output-contract (tc-resultp (typecheck instrs stack))
   (cond ((endp instrs) stack)
         ((primopp (car instrs))
          (let ((stepped (typechecker-step (car instrs) stack)))
            (if (typerrorp stepped)
                stepped
              (typecheck (cdr instrs) stepped))))
         ;; ((and (instr-ifp (car instrs))
         ;;       (unary-op-sym-stackp stack)
         ;;       (equal 'bool (car stack)))
         ;;  (let* ((instr (car instrs))
         ;;         (branch-stack (cdr stack))
         ;;         (conseq-stepped (typecheck (instr-if-conseq instr) branch-stack))
         ;;         (alt-stepped (typecheck (instr-if-alt instr) branch-stack)))
         ;;    (if (and (symbolic-stackp conseq-stepped)
         ;;             (symbolic-stackp alt-stepped)
         ;;             (equal conseq-stepped alt-stepped))
         ;;        (typecheck (cdr instrs) conseq-stepped)
         ;;      'typerror)))
         ;; ((and (instr-dipp (car instrs)) (consp stack))
         ;;  (let* ((first-stack (car stack))
         ;;         (rest-stack (cdr stack))
         ;;         (stepped (typecheck (instr-dip-instrs (car instrs)) rest-stack)))
         ;;    (if (symbolic-stackp stepped)
         ;;        (typecheck (cdr instrs) (cons first-stack stepped))
         ;;      'typerror)))
         (t 'typerror))))


(with-disable
 (fail-rawp
  failgasp
  failp
  interp-failurep
  interp-resultp
  stackp
  gasp
  instr-seqp
  instr-dipp
  instr-ifp
  instr-if=>def
  instr-dip=>def
  primopp
  tc-resultp
  typerrorp
  out-of-gasp
  symbolic-stackp
  (:DEFINITION INTERPRETER-STEP-DEFINITION-RULE)
  (:DEFINITION SUCCESS-GAS-DEFINITION-RULE)
  (:DEFINITION SUCCESS-STACK-DEFINITION-RULE))

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
         ;; ((and (instr-ifp (car instrs))
         ;;       (unary-op-stackp stack)
         ;;       (booleanp (car stack)))
         ;;  (let* ((instr (car instrs))
         ;;         (branch-stack (cdr stack))
         ;;         (stepped (interp (if (car stack)
         ;;                              (instr-if-conseq instr)
         ;;                              (instr-if-alt instr))
         ;;                          branch-stack
         ;;                          gas)))
         ;;    (if (interp-successp stepped)
         ;;        (interp (cdr instrs) (success-stack stepped) (success-gas stepped))
         ;;      stepped)))
         ;; ((and (instr-dipp (car instrs)) (consp stack))
         ;;  (let* ((first-stack (car stack))
         ;;         (rest-stack (cdr stack))
         ;;         (stepped (interp (instr-dip-instrs (car instrs)) rest-stack gas)))
         ;;    (if (interp-successp stepped)
         ;;        (interp (cdr instrs)
         ;;                (cons first-stack (success-stack stepped))
         ;;                (success-gas stepped))
         ;;      stepped)))
         (t 'typerror))))

(defthm typecheck-interp-progress
  (implies (and (symbolic-stackp sym-stack)
                (stackp stack)
                (instr-seqp ops)
                (reified-stackp sym-stack stack)
                (gasp gas)
                (not (typerrorp (typecheck ops sym-stack))))
           (let ((result (interp ops stack gas)))
             (and (not (typerrorp result))
                  (or (failgasp result)
                      (failp result)
                      (reified-stackp (typecheck ops sym-stack)
                                      (success-stack result)))))))
