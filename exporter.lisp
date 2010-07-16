;;;
;;; ECDB: Extended Clause Database System
;;; Tables of RAHD-generated clauses and exporting functions.
;;;
;;; ** Datastructure export and conversion functions **
;;;
;;;     Case exporting functions:   conjunctive formula --> explicit formula
;;;                                 explicit formula --> quantified Coq formula
;;;
;;;
;;; Written by Florent Kirchner
;;; Postdoctoral Researcher, INRIA Rennes - Bretagne Atlantique, France
;;; Contact: florent.kirchner@lix.polytechnique.fr, www.lix.polytechnique.fr/~fkirchner/
;;; 
;;; This file: began on         february-19-2010,
;;;            last updated on  april-9-2010.
;;;

(in-package ECDB)

;;;
;;; DUMP[-COQ]-CS: Primitive clause printing functions. 
;;;

(defun dump-cs (c)
  (format t "[cs:case-~A] ~A~%" 
          (aref rahd::*gs* rahd::*current-tactic-case* 0)
          c))

(defun dump-coq-cs (c)
  (format t "[coq-cs:case-~A] ~A~%" 
          (aref rahd::*gs* rahd::*current-tactic-case* 0)
          (make-coq-clause c)))

;;;
;;; FEED-DB: Add clause and a list of extended attributes to the database. The
;;; list corresponds to RAHD's *last-tactic-progress-lst*.
;;;

(defun feed-db (formula goal-key c attributes-list)
  (mapcar #'(lambda (al) 
              (push-clause-row (make-clause-row (getf al :case-id) goal-key c
                                                (getf al :cmf) nil (getf al :status))
                               (sxhash formula))) 
          attributes-list))


;;;
;;; MAKE-CONJ-CLAUSE-EXPLICIT: take the clause of a DNF-formula, and explicit
;;; its conjunctions. All connectors are binary.
;;;
;;; Ex: ((= x 1) (> x 1) (< x 1)) --> (:AND (= x 1) (:AND (> x 1) (< x 1)))
;;;

(defun make-conj-clause-explicit (c)
  (cond ((not (consp c)) nil)
        ((= (length c) 2)
         `(:AND ,(car c) ,(cadr c)))
        ((= (length c) 1)
         (car c))
        (t `(:AND ,(car c)
                  ,(make-conj-clause-explicit (cdr c))))))

;;;
;;; Predicate and term translation amount to infix operator transformation.:
;;; 
;;;     We take advantage of the RAHD pre-processing: predicates don't include
;;;     large inequalities or disequalities. Similarly, literals are assumed to
;;;     be division-less.
;;; 

(defparameter *predicate-symbols*
  '(< > =))

(defun parse-literal (l)
  (if (not (equal (length l) 3))
    (break "Bad literal translation: predicate is not binary."))
  (let ((predsym (first l))
        (lhs (parse-term (second l)))
        (rhs (parse-term (third l))))
    (if (not (member predsym *predicate-symbols*))
      (break "Bad literal translation: head symbol ~A is not one of ~A." predsym *predicate-symbols*))
    (format nil "~A ~A ~A" lhs predsym rhs)))

(defparameter *arith-symbols*
  '(* + -))

(defun parse-term (term)
  (cond ((not (listp term))
         (format nil "~A" term))
        ((not (>= (length term) 3))
         (break "Bad term translation: not enough operands in ~A" term))
        (t (let* ((op (first term))
                  (opd (parse-term (car (rest term))))
                  (opds (rest (rest term)))
                  ; Recursively parse the elements of opds, and insert op between each two.
                  (res (mapcan #'(lambda (x) (list op (parse-term x))) opds)))
             (if (not (member op *arith-symbols*))
               (break "Bad term translation: head symbol ~A is not one of ~A." op *arith-symbols*))
             (format nil "(~A~{ ~A~})" opd res)))))

(defun make-coq-clause* (ec)
  (cond ((endp ec) (format nil ""))
        ((not (equalp (car ec) ':AND))
         (format nil "~A" (parse-literal ec)))
        (t (format nil "~A /\\ ~A" 
                   (make-coq-clause* (cadr ec))
                   (make-coq-clause* (caddr ec))))))

;;;
;;; MAKE-COQ-CLAUSE+: take the clause of an explicit DNF-formula, and translate
;;; it into an unquantified Coq formula. Tail-recursive.
;;;
;;; Note that this function doubles all backslashes. Use PRINC or an enclosing
;;; FORMAT T to print correctly.
;;;
;;; Ex: (:AND (= x 1) (:AND (> x 1) (< x 1))) --> (= x 1) /\\ (> x 1) /\\ (< x 1)
;;;

(defun make-coq-clause+ (ec)
  (cond ((endp ec) (format nil ""))
        ((not (equalp (car ec) ':AND))
         (format nil "~A" (parse-literal ec)))
        (t (format nil "~A /\\ ~A" 
                   (make-coq-clause+ (cadr ec))
                   (make-coq-clause+ (caddr ec))))))

;;;
;;; MAKE-COQ-CONJ: take a clause and translate it into a quantified Coq formula.
;;;
;;; Ex: ((= x 1) (> x 1) (< x 1)) --> exists x, (x=1) /\ (x>1) /\ (x<1)
;;;

(defun make-coq-clause (c)
  (let* ((ec (make-conj-clause-explicit c))
         (cc (make-coq-clause+ ec))
         (var-list (rahd::all-vars-in-conj c)))
    ; From www.lispworks.com/documentation/HyperSpec/Body/22_cgd.htm
    (format nil "exists~{ ~A~}, ~A" var-list cc)))
