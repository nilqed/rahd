;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; ** Case-splitting routines, and some simple case manipulation functions **
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         22-July-2008,
;;;            last updated on  18-January-2011.
;;;

(in-package RAHD)

;;;
;;; WATERFALL-DISJ-TO-CNF: Convert a waterfall disjunction to an actual CNF 
;;;  formula suitable for calling (G ...).
;;;

(defun waterfall-disj-to-cnf (c)
  (let ((adj-c nil))
    (dolist (lit c)
      (let ((adj-lit
	     (if (equal (car lit) ':OR) 
		 (cdr lit)
	       (list lit))))
	(setq adj-c (cons adj-lit adj-c))))
    (reverse adj-c)))

;;;
;;; NUM-SOFT-INEQS: Count the number of soft inequalities in a 
;;;  case.
;;;

(defun num-soft-ineqs (c)
  (let ((out 0))
    (dolist (l c)
      (if (or (eq (car l) '>=)
	      (eq (car l) '<=))
	  (setq out (1+ out))))
    out))

;;;
;;; SPLIT-INEQS-CMF: A CMF for splitting soft inequalities.
;;;  It returns a :CASES form.
;;;

(defun split-ineqs-cmf (c &key atom max-splits)
  (if (= (num-soft-ineqs c) 0)
      c
    (multiple-value-bind 
	(splits-executed? formula)
	(split-ineqs-in-case c :atom atom :max-splits max-splits)
      (if splits-executed?
	  (cons ':CASES (drill-down formula))
	c))))

;;;
;;; SPLIT-INEQS-IN-CASE: Given a case, split its inequalities, 
;;;  returning a formula in RAHD implicit CNF.
;;; We return an MV-pair:
;;;  (splits-executed? . resulting-formula).
;;;

(defun split-ineqs-in-case (c &key atom max-splits)
  (let ((n (num-soft-ineqs c)))
    (if (or (= n 0)
	    (and (numberp atom)
		 (> atom n))
	    (and (numberp max-splits)
		 (< max-splits 1)))
	(values nil nil)
      (let ((out) (soft-ineq-id 0) (total-splits 0))
	(dolist (a c)
	  (let ((op (car a))
		(x (cadr a))
		(y (caddr a)))
	    (cond ((or (eq op '>=) (eq op '<=))
		   (if (or (and (integerp atom)
				(= soft-ineq-id atom))
			   (and (integerp max-splits)
				(< total-splits max-splits))
			   (and (not (numberp atom))
				(not (numberp max-splits))))
		       (progn
			 (setq out (cons
				    (case op
				      (>= `((> ,x ,y) (= ,x ,y)))
				      (<= `((< ,x ,y) (= ,x ,y))))
				    out))
			 (setq total-splits (1+ total-splits)))
		     (setq out (cons (list a) out)))
		   (setq soft-ineq-id (1+ soft-ineq-id)))
		  (t (setq out (cons (list a) out))))))
	(values (> total-splits 0)
		(when (> total-splits 0) out))))))
				
;;; Before drill down, we need to fire away NOT's and soft inequalities (<=, =>).
;;; Updated drill-down to be more optimized for dealing with unit clauses (01-March-2009).

(defun drill-down (o)
  (let ((unit-clauses (remove-if #'(lambda (x) (> (length x) 1)) o))
	(non-unit-clauses (remove-if #'(lambda (x) (= (length x) 1)) o)))

    (let ((unit-clauses-conjoined nil))
      (dolist (c unit-clauses)
	(setq unit-clauses-conjoined (cons (car c) unit-clauses-conjoined)))

      (if (= (length o) (length unit-clauses))
	  (list unit-clauses-conjoined)

	(let ((split-cases (drill-down* non-unit-clauses nil (length non-unit-clauses))))
	  (let ((final-o nil))
	    (dolist (c split-cases)
	      (setq final-o
		    (cons (append unit-clauses-conjoined c) final-o)))
	    (mapcar #'remove-duplicates final-o)))))))

(defun drill-down* (o a n)
  (cond ((not (consp o)) (if (= n (length a)) (list a) nil))
	(t (let ((cur-clause (car o)))
	     (cond ((not (consp cur-clause))
		    (drill-down* (cdr o) a n))
		   (t (let ((cur-hyp (car cur-clause)))
			(append
			 (drill-down* (cdr o) (cons cur-hyp a) n)
			 (drill-down* (cons (cdr cur-clause) (cdr o)) a n)))))))))

(defun expand-formula (c &key do-not-split-ineqs?)
  (cond ((endp c) nil)
	(t (let ((expanded-clause (expand-clause (car c) nil
						 :do-not-split-ineqs? do-not-split-ineqs?)))
	     (cons expanded-clause (expand-formula (cdr c)
						   :do-not-split-ineqs? do-not-split-ineqs?))))))

(defun expand-clause (cl cur-clause &key do-not-split-ineqs?)
  (cond ((endp cl) cur-clause)
	(t (let ((cur-expanded-lit (expand-special-syms 
				    (car cl)
				    :do-not-split-ineqs?
				    do-not-split-ineqs?)))
	     (if (consp (car cur-expanded-lit))
		 (expand-clause (cdr cl) 
				(union cur-expanded-lit cur-clause)
				:do-not-split-ineqs? do-not-split-ineqs?)
	       (expand-clause (cdr cl)
			      (union (list cur-expanded-lit) cur-clause)
			      :do-not-split-ineqs? do-not-split-ineqs?))))))
      

; 19-Sept-2008 added TERM-TO-BIN-OPS here.
; 23-Nov-2008 added EXPAND-DIVS here.

(defun expand-special-syms (lit &key do-not-split-ineqs?)
  (let ((cur-op (car lit)))
    (cond ((not (equal cur-op 'NOT))
	   (let ((cur-x (expand-divs (term-to-bin-ops (cadr lit))))
		 (cur-y (expand-divs (term-to-bin-ops (caddr lit)))))
	     (if do-not-split-ineqs?
		 `(,cur-op ,cur-x ,cur-y)
	       (case cur-op
		 (<= `((< ,cur-x ,cur-y)
		       (= ,cur-x ,cur-y)))
		 (>= `((> ,cur-x ,cur-y)
		       (= ,cur-x ,cur-y)))
		 (otherwise `(,cur-op ,cur-x ,cur-y))))))
	  (t (let ((cur-atom (cadr lit)))
	       (let ((cur-r (car cur-atom))
		     (cur-x (expand-divs (term-to-bin-ops (cadr cur-atom))))
		     (cur-y (expand-divs (term-to-bin-ops (caddr cur-atom)))))
		 (case cur-r
		       (<= `(> ,cur-x ,cur-y))
		       (>= `(< ,cur-x ,cur-y))
		       (=  `((< ,cur-x ,cur-y)
			     (> ,cur-x ,cur-y)))
		       (<  (expand-special-syms `(>= ,cur-x ,cur-y)
						:do-not-split-ineqs? do-not-split-ineqs?))
		       (>  (expand-special-syms `(<= ,cur-x ,cur-y)
						:do-not-split-ineqs? do-not-split-ineqs?))
		       (otherwise (break "Bad symbol in goal.")))))))))


;;;
;;; NEG-LIT?: Is a literal negative (e.g., preceded by a NOT?).
;;;

(defun neg-lit? (l)
  (equal (caar l) 'not))

;;;
;;; Check that our top-level formulas are in our special CNF input format.
;;;

(defun top-level-syntax-check (cs)
  (let ((form-ok (and (consp cs) (> (length cs) 0))))
    (when form-ok
      (dolist (c cs)
	(let ((clause-ok (and (consp c) (> (length c) 0))))
	  (when clause-ok 
	    (dolist (l c)
	      (cond ((not (consp l)) (setq clause-ok nil))
		    ((consp l)
		     (let ((lit-in-question
			    (if (equal (car l) 'NOT)
				(cadr l)
			      l)))
		       (if (not (= (length lit-in-question) 3))
			   (setq clause-ok nil)
			 (let ((op (car lit-in-question))
			       (x  (cadr lit-in-question))
			       (y  (caddr lit-in-question)))
			   (declare (ignorable x y))
			   (if (or (not (member op '(= < > <= >=)))
				   (not (and (rationalfunctionp (term-to-bin-ops x))
					     (rationalfunctionp (term-to-bin-ops y)))))
			       (setq clause-ok nil)))))))))
	  (setq form-ok (and form-ok clause-ok)))))
    form-ok))

(defun rationalfunctionp (p)
  (cond ((rationalp p) t)
	((and (symbolp p) (not (member p '(= <= >= + - *)))) t)
	((and (consp p) (= (length p) 3)
	      (and (member (car p) '(+ - * /))
		   (if (equal (car p) '/)
		       (not (equal (canonicalize-poly (caddr p)) 0))
		     t)) ; More complicated for eliminating explicit divs by 0.
	      (and (rationalfunctionp (cadr p))
		   (rationalfunctionp (caddr p)))))
	(t nil)))
	      
	 
;;;
;;; ALL-VARS-IN-CNF: Return all variables in RAHD top-level formula.
;;; 

(defun all-vars-in-cnf (cs)
  (let ((cs-conj nil)
	(cs* (if (eq (car cs) ':CASES) (cdr cs) cs)))
    (dolist (c cs*)
      (dolist (l c)
	(setq cs-conj (append (list l) cs-conj))))
    (all-vars-in-conj cs-conj)))


;;;
;;; A stub for division expansion.
;;;

(defun expand-divs (x) x)

;;;
;;; Given a conjunction, its extracted equalities, and a predicate
;;; that maps {(= LHS RHS) | LHS, RHS are terms} to 2, return the result of
;;; applying (LHS -> RHS) to every literal s.t. (= LHS RHS) satisfies
;;; the predicate passed.
;;;
;;; For example, to only apply equalities to terms that will rewrite
;;; variables with numerals, do:
;;;
;;;  (subst-eqs c eqs #'(lambda (eq) (numberp (caddr eq)))).
;;;

(defun subst-eqs (c eqs pred)
  (cond ((endp eqs) (remove-duplicates c :test 'equal))
	(t (let ((cur-eq (car eqs)))
	     (if (funcall pred cur-eq)
		 (progn
		   (add-vt-binding (cadr cur-eq) (caddr cur-eq))
		   (subst-eqs 
		    (subst (caddr cur-eq) (cadr cur-eq) c)
		    (cdr eqs)
		    pred))
	       (subst-eqs c (cdr eqs) pred))))))

;;;
;;; Given a conjunction, return the result of rewriting the conjunction with
;;; each equality the conjunction contains that has a number as its RHS.
;;;

(defun demodulate-numerically (c)
  (subst-eqs c (gather-eqs c) 
	     #'(lambda (eq) (and (symbolp (cadr eq)) (numberp (caddr eq))))))

;;;
;;; Is a literal ground?
;;;

(defun lit-ground? (l)
  (and (term-ground? (cadr l))
       (term-ground? (caddr l))))

(defun term-ground? (term)
  (cond 
   ((equal term nil) t)
   ((numberp term) t)
   ((symbolp term)
    (if (member term '(+ - * / EXACT-REAL-EXPT)) t nil))
   (t (and (term-ground? (car term))
	   (term-ground? (cdr term))))))
	
;;;
;;; Simplify ground literals in a conjunction.
;;; Note: We also simplify ground terms in non-ground literals.
;;;       * We also simplify (= X X) to T.

(defun simplify-ground-lits (c)
  (mapcar #'(lambda (l)
	      (if (lit-ground? l)
		  (eval l)
		(let ((cur-op (car l))
		      (cur-x  (cadr l))
		      (cur-y  (caddr l)))
		  (if (and (equal cur-op '=)
			   (equal cur-x cur-y))
		      T
		      `(,cur-op
			,(if (term-ground? cur-x)
			     (eval cur-x)
			     cur-x)
			,(if (term-ground? cur-y)
			     (eval cur-y)
			     cur-y))))))
	  c))

;;;
;;; Remove `t's and `nils' from a conjunction.
;;; If c contains `nil' then we return `(:UNSAT (:UNSAT-WITNESS nil)).
;;;

(defun remove-truth-vals (c result)
  (cond ((endp c) result)
	(t (let ((cur-l (car c)))
	     (cond ((equal cur-l nil) '(:UNSAT (:UNSAT-WITNESS nil)))
		   ((equal cur-l t)
		    (remove-truth-vals (cdr c) result))
		   (t (remove-truth-vals (cdr c)
					 (cons cur-l result))))))))

(defun remove-truth-vals* (c)
  (let ((result (remove-truth-vals c nil)))
    (cond ((and (consp result) (equal (car result) ':UNSAT))
	   result)
	  ((equal result nil)

	   ;;; This means the case has been reduced to an implicit T, 
	   ;;; and thus the installed goal is SAT.

	   '(:SAT :CASE-REDUCED-TO-EMPTY-CONJUNCTION))
	  (t (reverse result)))))

(defun simplify-ground-lits+rtv (c)
  (remove-truth-vals*
   (simplify-ground-lits c)))

;;;
;;; A little term simplifier.  We do these main things:
;;;
;;;  (1) reduce (- x x) to 0,
;;;  (2) reduce (+ x (- x)) to 0,
;;;  (4) reduce (* x 0) to 0,
;;;  (5) reduce (+ x 0) to x,
;;;  (6) reduce (- x 0) to x,
;;;  (7) reduce (* x 1) to x.
;;;
;;; Note that all terms must be forced into binary function notation via
;;; TERM-TO-BIN-OPS before calls to this term simplifier.
;;;

(defun simplify-term (term last-val)
  (cond ((numberp term) term)
	((symbolp term) term)
	((equal term nil) nil)
	((equal term last-val) term)
	(t (let ((cur-op (car term))
		 (x (cadr term))
		 (y (caddr term)))
	     (case cur-op
		   (* (cond ((or (equal x 0) (equal y 0)) 0)
			    ((equal x 1) y)
			    ((equal y 1) x)
			    ((and (equal x y)
				  (consp x)
				  (equal (car x) '-) 
				  (equal (cadr x) 0)) (simplify-term `(* ,(caddr x) ,(caddr x)) nil)) ; (* (- 0 a) (- 0 a)) --> (* a a).
			    (t (simplify-term `(* ,(simplify-term x nil)
						  ,(simplify-term y nil))
					      term))))
		   (+ (cond ((equal x 0) y)
			    ((equal y 0) x)
			    ((equal x `(- 0 ,y)) 0)
			    ((equal y `(- 0 ,x)) 0)
			    (t (simplify-term `(+ ,(simplify-term x nil)
						  ,(simplify-term y nil))
					      term))))
		   (- (cond ((equal y 0) x)
			    ((equal x y) 0)
			    (t (simplify-term `(- ,(simplify-term x nil)
						  ,(simplify-term y nil))
					      term))))
		   (otherwise
		    (simplify-term `(,cur-op ,(simplify-term (cadr term) nil)
					     ,(simplify-term (caddr term) nil))
				   term)))))))

;;;
;;; Expand term to binary ops (e.g. make (* x y z) (* x (* y z))).
;;;

(defun term-to-bin-ops (tm)
  (cond ((equal tm nil) nil)
	((numberp tm) tm)
	((symbolp tm) tm)
	((= (length tm) 3) `(,(car tm) ,(term-to-bin-ops (cadr tm))
			     ,(term-to-bin-ops (caddr tm))))
	((= (length tm) 2) (break "Invalid term: Cannot make ops binary."))
	(t (case (car tm)
		 (* (op-to-bin-op tm '*))
		 (+ (op-to-bin-op tm '+))
		 (otherwise (break "Invalid term: Cannot make ops binary."))))))

(defun op-to-bin-op (tm op)
  (cond ((equal tm nil) nil)
	((numberp tm) tm)
	((symbolp tm) tm)
	(t `(,op ,(term-to-bin-ops (cadr tm))
		 ,(term-to-bin-ops (cons op (cddr tm)))))))

;;;
;;; Simplify a literal.
;;;

(defun arith-simplify-lit (lit)
  `(,(car lit) 
    ,(simplify-term (term-to-bin-ops (cadr lit)) nil) 
    ,(simplify-term (term-to-bin-ops (caddr lit)) nil)))

;;;
;;; Simplify a conjunction (case) arithmetically.
;;;

(defun arith-simplify-case (c)
  (mapcar #'arith-simplify-lit c))
    

;;;
;;; TOP-LEVEL-FORMULA-TO-BIN-OPS:
;;;

(defun tlf-to-bin-ops (f)
  (let ((out nil))
    (let ((out-clause nil))
      (dolist (c f)
	(setq out-clause nil)
	(let ((out-lit nil))
	  (dolist (l c)
	    (setq out-lit
		  (list (car l)
			(term-to-bin-ops (cadr l))
			(term-to-bin-ops (caddr l))))
	    (setq out-clause
		  (cons out-lit out-clause))))
	(setq out (cons out-clause out))))
    out))

;;;
;;; PTA: Polynomial in generic (possibly non-binary) prover notation
;;;  to algebraic representation.
;;;

(defun pta (p)
  (poly-prover-rep-to-alg-rep (term-to-bin-ops p)))


#|
;;;
;;; Problematic terms:
;;;

(defparameter *tm*
  '(+ (* (- 1 (* 1 1 1 1)) (- 1 (* 1 d)) (- (* 1 d) (* 1 1))
          (- (* 1 d) (* 1 1)))
       (* (* 2 1 1) (- (* 1 d) (* 1 1)) (- 1 (* 1 1)) (- 1 d) (- 1 d))
       (* (- (* 1 1 1 1) (* 1 1 d d)) (- 1 (* 1 d)) (- 1 1) (- 1 1))))

(defparameter *tm2*
  '(+ (* (- 1 (* 0 0 b b)) (- 1 (* 0 1)) (- (* 0 1) (* b 0))
          (- (* 0 1) (* b 0)))
       (* (* 2 0 b) (- (* 0 1) (* 0 b)) (- 1 (* 0 b)) (- 0 1) (- 0 1))
       (* (- (* 0 0 b b) (* 0 0 1 1)) (- 1 (* 0 1)) (- 0 b) (- 0 b))))
#|
;;;
;;; Case study problem I
;;;

;time REAL_SOS
; `&0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1 /\
;  &0 <= c /\ c <= &1 /\ &0 <= d /\ d <= &1
;   ==> (&1 - a pow 2 * b pow 2) * (&1 - c * d) * (a * d - b * c) pow 2 +
;       &2 * a * b * (c * d - a * b) * (&1 - a * b) * (c - d) pow 2 +
;       (a pow 2 * b pow 2 - c pow 2 * d pow 2) *
;       (&1 - c * d) * (a - b) pow 2 >= &0`;;


(defparameter *hyps*
  '( ((> a 0) (= a 0))
     ((> b 0) (= b 0))
     ((> c 0) (= c 0))
     ((> d 0) (= d 0))
     ((< a 1) (= a 1))
     ((< b 1) (= b 1))
     ((< c 1) (= c 1))
     ((< d 1) (= d 1))))

(defparameter *negated-goal*
  '(((> a 0) (= a 0))
    ((> b 0) (= b 0))
    ((> c 0) (= c 0))
    ((> d 0) (= d 0))
    ((< a 1) (= a 1))
    ((< b 1) (= b 1))
    ((< c 1) (= c 1))
    ((< d 1) (= d 1))
    ((< (+ (* (- 1 (* a a b b)) (- 1 (* c d)) (- (* a d) (* b c)) (- (* a d) (* b c)))
	   (* (* 2 a b) (- (* c d) (* a b)) (- 1 (* a b)) (- c d) (- c d))
	   (* (- (* a a b b) (* c c d d)) (- 1 (* c d)) (- a b) (- a b))) 
	0))))
     




;;;
;;; The cases not ruled out by simple equality incons elimination:
;;;

|#
((< d 1) (< c 1) (< b 1) (< a 1) (= d 0) (= c 0) (= b 0) (= a 0))
((= d 1) (< c 1) (< b 1) (< a 1) (> d 0) (= c 0) (= b 0) (= a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (= c 0) (= b 0) (= a 0))
((< d 1) (= c 1) (< b 1) (< a 1) (= d 0) (> c 0) (= b 0) (= a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (= d 0) (> c 0) (= b 0) (= a 0))
((= d 1) (= c 1) (< b 1) (< a 1) (> d 0) (> c 0) (= b 0) (= a 0))
((< d 1) (= c 1) (< b 1) (< a 1) (> d 0) (> c 0) (= b 0) (= a 0))
((= d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (= b 0) (= a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (= b 0) (= a 0))
((< d 1) (< c 1) (= b 1) (< a 1) (= d 0) (= c 0) (> b 0) (= a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (= d 0) (= c 0) (> b 0) (= a 0))
((= d 1) (< c 1) (= b 1) (< a 1) (> d 0) (= c 0) (> b 0) (= a 0))
((< d 1) (< c 1) (= b 1) (< a 1) (> d 0) (= c 0) (> b 0) (= a 0))
((= d 1) (< c 1) (< b 1) (< a 1) (> d 0) (= c 0) (> b 0) (= a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (= c 0) (> b 0) (= a 0))
((< d 1) (= c 1) (= b 1) (< a 1) (= d 0) (> c 0) (> b 0) (= a 0))
((< d 1) (< c 1) (= b 1) (< a 1) (= d 0) (> c 0) (> b 0) (= a 0))
((< d 1) (= c 1) (< b 1) (< a 1) (= d 0) (> c 0) (> b 0) (= a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (= d 0) (> c 0) (> b 0) (= a 0))
((= d 1) (= c 1) (= b 1) (< a 1) (> d 0) (> c 0) (> b 0) (= a 0))
((< d 1) (= c 1) (= b 1) (< a 1) (> d 0) (> c 0) (> b 0) (= a 0))
((= d 1) (< c 1) (= b 1) (< a 1) (> d 0) (> c 0) (> b 0) (= a 0))
((< d 1) (< c 1) (= b 1) (< a 1) (> d 0) (> c 0) (> b 0) (= a 0))
((= d 1) (= c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (= a 0))
((< d 1) (= c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (= a 0))
((= d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (= a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (= a 0))
((< d 1) (< c 1) (< b 1) (= a 1) (= d 0) (= c 0) (= b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (= d 0) (= c 0) (= b 0) (> a 0))
((= d 1) (< c 1) (< b 1) (= a 1) (> d 0) (= c 0) (= b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (= a 1) (> d 0) (= c 0) (= b 0) (> a 0))
((= d 1) (< c 1) (< b 1) (< a 1) (> d 0) (= c 0) (= b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (= c 0) (= b 0) (> a 0))
((< d 1) (= c 1) (< b 1) (= a 1) (= d 0) (> c 0) (= b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (= a 1) (= d 0) (> c 0) (= b 0) (> a 0))
((< d 1) (= c 1) (< b 1) (< a 1) (= d 0) (> c 0) (= b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (= d 0) (> c 0) (= b 0) (> a 0))
((= d 1) (= c 1) (< b 1) (= a 1) (> d 0) (> c 0) (= b 0) (> a 0))
((< d 1) (= c 1) (< b 1) (= a 1) (> d 0) (> c 0) (= b 0) (> a 0))
((= d 1) (< c 1) (< b 1) (= a 1) (> d 0) (> c 0) (= b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (= a 1) (> d 0) (> c 0) (= b 0) (> a 0))
((= d 1) (= c 1) (< b 1) (< a 1) (> d 0) (> c 0) (= b 0) (> a 0))
((< d 1) (= c 1) (< b 1) (< a 1) (> d 0) (> c 0) (= b 0) (> a 0))
((= d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (= b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (= b 0) (> a 0))
((< d 1) (< c 1) (= b 1) (= a 1) (= d 0) (= c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (= a 1) (= d 0) (= c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (= b 1) (< a 1) (= d 0) (= c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (= d 0) (= c 0) (> b 0) (> a 0))
((= d 1) (< c 1) (= b 1) (= a 1) (> d 0) (= c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (= b 1) (= a 1) (> d 0) (= c 0) (> b 0) (> a 0))
((= d 1) (< c 1) (< b 1) (= a 1) (> d 0) (= c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (= a 1) (> d 0) (= c 0) (> b 0) (> a 0))
((= d 1) (< c 1) (= b 1) (< a 1) (> d 0) (= c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (= b 1) (< a 1) (> d 0) (= c 0) (> b 0) (> a 0))
((= d 1) (< c 1) (< b 1) (< a 1) (> d 0) (= c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (= c 0) (> b 0) (> a 0))
((< d 1) (= c 1) (= b 1) (= a 1) (= d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (= b 1) (= a 1) (= d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (= c 1) (< b 1) (= a 1) (= d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (= a 1) (= d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (= c 1) (= b 1) (< a 1) (= d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (= b 1) (< a 1) (= d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (= c 1) (< b 1) (< a 1) (= d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (= d 0) (> c 0) (> b 0) (> a 0))
((= d 1) (= c 1) (= b 1) (= a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (= c 1) (= b 1) (= a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((= d 1) (< c 1) (= b 1) (= a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (= b 1) (= a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((= d 1) (= c 1) (< b 1) (= a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (= c 1) (< b 1) (= a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((= d 1) (< c 1) (< b 1) (= a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (= a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((= d 1) (= c 1) (= b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (= c 1) (= b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((= d 1) (< c 1) (= b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (= b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((= d 1) (= c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (= c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((= d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0))
((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0))

;;; 81 above to check.

;;; How many are 0-ary (e.g. ground) problems after substitution?

(length (filter-by-num-eqs (cadar (clear-simply-incons (drill-down *hyps*) nil nil)) 4))
16

;;; How many are univariate problems after substitution?

(length (filter-by-num-eqs (cadar (clear-simply-incons (drill-down *hyps*) nil nil)) 3))
32

;;; How many are bivariate?

(length (filter-by-num-eqs (cadar (clear-simply-incons (drill-down *hyps*) nil nil)) 2))
24

;;; How many are trivariate?

(length (filter-by-num-eqs (cadar (clear-simply-incons (drill-down *hyps*) nil nil)) 1))
8

;;; How many contain no equalities?
;;; Only one of course, our open relaxation!

(filter-by-num-eqs (cadar (clear-simply-incons (drill-down *hyps*) nil nil)) 0)
(((< d 1) (< c 1) (< b 1) (< a 1) (> d 0) (> c 0) (> b 0) (> a 0)))


(defun expand-soft-ineqs (o)
  (cond ((endp o) nil)
	(t (let ((cur-lit (car o)))
	     (let ((cur-x (cadr cur-lit))
		   (cur-y (caddr cur-lit)))
	       (let ((modified-lit
		      (case (car cur-lit)
			    ('<=  `((< ,cur-x ,cur-y)
				    (= ,cur-x ,cur-y)))
			    ('>=  `((> ,cur-x ,cur-y)
				    (= ,cur-x ,cur-y)))
			    (otherwise cur-lit))))
		 (cons modified-lit (expand-soft-ineqs (cdr o)))))))))
				  
  



|#
