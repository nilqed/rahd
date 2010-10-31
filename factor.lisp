;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; CMF based on multivariate factorisation and sign determination.
;;;  * Requires maxima-rahd.lisp has been loaded.
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         25-June-2010,
;;;            last updated on  27-June-2010.
;;;

;;;
;;; FACTOR-SIGN-CASE: Given a case, factor all of its polynomials,
;;;  and adjoin sign constraints if the factorisations prove a polynomial
;;;  is either PSD, PD, -PSD or -PD.
;;;

(defun factor-sign-case (c)
  (let ((out nil))
    (dolist (l c)
      (multiple-value-bind 
	  (p p-factored p-sign-op)
	  (factor-sign-lit l)
	(declare (ignorable p-factored))
	(when p-sign-op
	  (setq out (append `((,p-sign-op ,p 0)) out)))))
    (let ((new-c (union out c)))
      (if (and (subsetp c new-c)
	       (subsetp new-c c))
	  c
	new-c))))

;;;
;;; FACTOR-SIGN-LIT: Given a single literal, return a result of the form
;;;   (mv p q '>=)
;;;  if p is factored as q and q can be easily seen to be PSD.
;;; Similarly, we check for q to be PD, -PSD, -PD.
;;; If we can't deduce any sign of p, we return (mv p q nil).
;;;

(defun factor-sign-lit (l)
  (let ((x (cadr l)) (y (caddr l)))
    (let ((p (if (equal y 0) x `(- ,x ,y))))
      (let* ((q (factor p))
	     (sq (deduce-sign q)))
	(values p q sq)))))

;;;
;;; DEDUCE-SIGN p:
;;; Given a polynomial p in extended EXPT notation, try to deduce 
;;;  its sign, returning either <,<=,=,>=,>, or nil.
;;;

(defun deduce-sign (p)
  (cond ((numberp p) (n-sign-rel p))
	((consp p)
	 (let ((op (car p))
	       (x (cadr p))
	       (y (caddr p)))
	   (let ((sign-of-x (deduce-sign x)))
	     (cond
	      ((and (equal op 'EXPT)
		    (numberp y)
		    (evenp y))
	       (case sign-of-x
		 ((< >) '>)
		 ((<= >= nil) '>=)
		 ((=) '=)))
	      ((and (equal op 'EXPT)
		    (numberp y)
		    (oddp y))
	       sign-of-x)
	      ((equal op '+)
	       (let ((sign-of-y (deduce-sign y)))
		 (sign-of-+ sign-of-x sign-of-y)))
	      ((equal op '*)
	       (let ((sign-of-y (deduce-sign y)))
		 (sign-of-* sign-of-x sign-of-y)))
	      (t nil)))))))

;;;
;;; SIGN-OF-+: Given two symbolic signs, return the sign of
;;;  their sum (returning nil if we can deduce nothing).
;;;

(defun sign-of-+ (sx sy)
  (case sx
    (> (case sy
	 ((> >= =) '>)
	 (otherwise nil)))
    (>= (case sy
	  (> '>)
	  ((>= =) '>=)
	  (otherwise nil)))
    (= sy)
    (<= (case sy
	  (< '<)
	  ((<= =) '<=)
	  (otherwise nil)))
    (< (case sy
	 ((< <= =) '<)
	 (otherwise nil)))
    (otherwise nil)))
	
;;;
;;; SIGN-OF-*: Given two symbolic signs, return the sign of
;;;  their product (returning nil if we can deduce nothing).
;;;

(defun sign-of-* (sx sy)
  (cond ((or (not sx) (not sy)) nil)
	(t
	 (case sx
	   (> (case sy
		(> '>)
		(>= '>=)
		(= '=)
		(< '<)
		(<= '<=)))
	   (>= (case sy
		 (> '>=)
		 (>= '>=)
		 (= '=)
		 (< '<=)
		 (<= '<=)))
	   (= '=)
	   (<= (case sy
		 (> '<=)
		 (>= '<=)
		 (= '=)
		 (< '>=)
		 (<= '>=)))
	   (< (case sy
		(> '<)
		(>= '<=)
		(= '=)
		(<= '>=)
		(< '>)))))))
	 
;;;
;;; N-SIGN-REL: Given a number n, return a relation for its sign
;;;  ('> if (n > 0), etc.).
;;;

(defun n-sign-rel (n)
  (cond ((> n 0) '>)
	((= n 0) '=)
	((< n 0) '<)))