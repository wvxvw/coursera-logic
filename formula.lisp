;; YACC Common Lisp implementation is the courtesy of:
;; http://www.pps.univ-paris-diderot.fr/~jch/software/cl-yacc/

(defpackage coursera-logic
  (:use cl yacc)
  (:export
   #:equivalentp #:impliesp #:reducesp #:defexpression
   #:eitherp #:bothp #:notp #:validp #:unsatisfiablep
   #:satisfiesp))

(in-package :coursera-logic)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun infix->prefix (a b c) (list b a c))
  (defun second-arg (a b c)
    (declare (ignore a c)) b))

(defun logic-expression-lexer (stream)
  (let ((translations (make-hash-table)))
    (loop :for (key . value) :in
       '((#\( . \()
         (#\) . \))
         (#\∧ . bothp)
         (#\¬ . notp)
         (#\⇒ . impliesp)
         (#\∨ . eitherp)
         (#\⇔ . equivalentp)
         (#\⇐ . reducesp)) :do
       (setf (gethash key translations) value
             (gethash (intern (coerce (list key) 'string))
                      translations) value))
    (labels ((%intern-id (chars)
               (intern (nstring-upcase (coerce (nreverse chars) 'string))))
             (%read-token ()
               (loop
                  :with collected := nil
                  :for token := (read-char stream nil nil) :do
                  (cond
                    ((null token)
                     (return (when collected (%intern-id collected))))
                    ((gethash token translations)
                     (return
                       (if collected
                           (progn
                             (unread-char token stream)
                             (%intern-id collected))
                           (intern
                            (make-string 1 :initial-element token)))))
                    ((member token '(#\Space #\Tab #\Return #\Rubout))
                     (when collected (return (%intern-id collected))))
                    (t (push token collected))))))
      
      (lambda ()
        (let* ((key (%read-token))
               (value (or (gethash key translations) key)))
          ;; (format t "~&reading: ~s" value)
          (if (null key)
              (values nil nil)
              (let ((terminal (if (member key '(\( \) ∧ ¬ ⇒ ∨ ⇔ ⇐)) key 'id)))
                (values terminal value))))))))

(yacc:define-parser *logic-expression-parser* (:start-symbol exp)
  (:terminals (id \( \) ∧ ¬ ∨ ⇒ ⇔ ⇐))
  (:precedence ((:left ¬) (:left ∧ ∨) (:left ⇒ ⇔ ⇐)))
  
  (exp
   (exp ∧ exp #'infix->prefix)
   (exp ∨ exp #'infix->prefix)
   (exp ⇒ exp #'infix->prefix)
   (exp ⇔ exp #'infix->prefix)
   (exp ⇐ exp #'infix->prefix)
   term)
  
  (term
   id
   (¬ exp #'list)
   (\( exp \) #'second-arg)))

(defun equivalentp (a b) (eql a b))

(defun impliesp (a b) (or (not a) (eql a b)))

(defun reducesp (a b) (or (not b) (eql a b)))

(defun eitherp (a b) (or a b))

(defun bothp (a b) (and a b))

(defun notp (a) (not a))

(defun int->bools (int len)
  (loop :repeat len :collect
     (prog1 (= 1 (logand 1 int))
         (setf int (ash int -1)))))

(defun count-variables (exp)
  (let ((vars (make-hash-table)))
    (labels ((%count-variables (exp)
               (destructuring-bind (func arg0 &optional arg1) exp
                 (declare (ignore func))
                 (cond
                   ((and (symbolp arg0) (symbolp arg1) arg1)
                    (setf (gethash arg0 vars) t)
                    (setf (gethash arg1 vars) t))
                   ((and (symbolp arg0) arg1)
                    (setf (gethash arg0 vars) t)
                    (%count-variables arg1))
                   ((and (symbolp arg1) arg1)
                    (setf (gethash arg1 vars) t)
                    (%count-variables arg0))
                   ((symbolp arg0)
                    (setf (gethash arg0 vars) t))
                   (arg1
                    (%count-variables arg0)
                    (%count-variables arg1))
                   (t (%count-variables arg0))))))
      (%count-variables exp)
      (loop :for key :being :the :hash-key :of vars :collect key))))

(defun validp (len expression)
  (loop
     :for var :from 0 :below (expt 2 len)
     :unless (apply expression (int->bools var len)) :do
     (return)
     :finally (return t)))

(defun unsatisfiablep (len expression)
  (loop
     :for var :from 0 :below (expt 2 len)
     :when (apply expression (int->bools var len)) :do
     (return)
     :finally (return t)))

(defun satisfiesp (values expression)
  (apply expression values))

(defmacro defexpression (name expression)
  (multiple-value-bind (vars raw) (parse-expression expression)
    `(defun ,name ,vars ,raw)))

(defmacro defexpression-group (name &rest expressions)
  (loop
     :with total-vars := nil :and total-exp := nil
     :for exp :in expressions :do
     (multiple-value-bind (vars raw) (parse-expression exp)
       (setf total-vars (nunion total-vars vars)
             total-exp (cons raw total-exp)))
     :finally (return `(defun ,name ,total-vars (and ,@total-exp)))))

(defun parse-expression (string)
  (let* ((raw (yacc:parse-with-lexer
              (logic-expression-lexer
               (make-string-input-stream string)) *logic-expression-parser*))
         (vars (count-variables raw)))
    (values vars raw)))

(defun num-truth-assignments (expression numvars)
  (loop
     :for i :from 0 :below (expt 2 numvars)
     :when (apply expression (int->bools i numvars))
     :count i))

(defun entailsp (exp-group entailed)
  (loop
     :with total-vars := nil :and total-exp := nil
     :for exp :in exp-group :do
     (multiple-value-bind (vars raw) (parse-expression exp)
       (setf total-vars (nunion total-vars vars)
             total-exp (cons raw total-exp)))
     :finally
     (return
       (multiple-value-bind (vars func) (parse-expression entailed)
         (declare (ignore vars))
         (loop
            :with entailing :=
            (eval `(lambda ,total-vars
                     (let ((fs (and ,@total-exp)))
                       (or (not fs) (eql fs ,func)))))
            :and nargs := (length total-vars)
            :for i :from 0 :below (expt 2 nargs)
            :unless (apply entailing (int->bools i nargs)) :do
            (return)
            :finally (return t))))))
;; tests

(defexpression exercise-0 "(q⇒(r∧¬s))∧s")

(defexpression exercise-1 "(q⇒(r∧¬s))∨(r⇒(q∧¬s))")

(defexpression-group exercise-2 "r⇒q" "p⇒r" "s⇒s")

(defexpression-group exercise-3 "a⇒b" "b⇒c" "c⇒¬a")

(defexpression exercise-4 "(p ∧ q) ∨ (¬p ∧ ¬q)")

(defexpression exercise-5 "(p ∧ ¬q)∨ ¬p∨ q")

(defexpression exercise-6 "(¬r ∨ x ∨ ¬s) ∧ (r ⇒ s) ∧ ¬(r ⇒ x)")

(defexpression exercise-7 "(¬q ∧ (¬(h ⇒q) ∨ (¬q ∧h))) ∨ (¬h ∧ ¬q) ∨ ¬(¬q ∧ ¬h)")

(entailsp '("r⇒q" "p⇒r" "s⇒s") "p⇒r")
