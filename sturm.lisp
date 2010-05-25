;;;
;;; Univariate Sturm Theory and Cauchy Bound based Real Root Isolation
;;;
;;;   including: partial derivatives for polynomials in Q[\vec{x}],
;;;              derivations of univariate Sturm chains,
;;;              extraction of sign change sequences from evaluated Sturm chains,
;;;              square-free part reduction for univariate polynomials,
;;;              local determination of number of real roots of a univariate 
;;;                polynomial in a closed real interval with rational endpoints,
;;;              global determination of number of real roots of a univariate 
;;;                polynomial in ]-inf, +inf[ using Cauchy root bounds,
;;;              univariate exhaustive real root isolation w.r.t. pairwise disjount
;;;                sequence of root bounding rational intervals
;;;
;;;    for
;;; 
;;;     RAHD: Real Algebra in High Dimensions
;;;   
;;;   v0.6,
;;;
;;; A proof procedure for the existential theory of real closed fields.
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: (g.passmore@ed.ac.uk . http://homepages.inf.ed.ac.uk/s0793114/)
;;;
;;;
;;; This file: began on         16-July-2008,
;;;            last updated on  25-May-2010.
;;;

(in-package RAHD)

;;;
;;; DP/DV: Given a polynomial p and a variable ID v (w.r.t. *VARS-TABLE*),
;;; return the partial derivative of p w.r.t. v.
;;;

(defun dp/dv (p v)
  (cond ((endp p) nil)
	(t (let ((cur-m (car p)))
	     (let ((cur-c  (car cur-m))
		   (cur-pp (cdr cur-m)))
	       (let ((dcur-pp/dv (dpp/dv cur-pp v nil)))
		 (let ((d-scalar (car dcur-pp/dv))
		       (d-pp (cdr dcur-pp/dv)))
		   (poly-zsimp 
		    (cons `(,(s* cur-c d-scalar) . ,d-pp)
			  (dp/dv (cdr p) v))))))))))
  
;;; 
;;; DPP/DV: Given a power-product pp and a variable ID v (w.r.t. *VARS-TABLE*),
;;; return the partial derivative of pp w.r.t. v.  
;;;
;;; Note that we return a monomial (e.g. `(,coeff . ,power-product)).
;;; Note that the accumulator, accum-pp, should be initially nil.
;;;

(defun dpp/dv (pp v accum-pp)
  (cond ((endp pp) nil)
	(t (let ((cur-v (caar pp))
		 (cur-p (cdar pp)))
	     (cond ((= cur-v v)
		    `(,cur-p . ,(append accum-pp
					(cons `(,v . ,(1- cur-p))
					      (cdr pp)))))
		   ((< cur-v v) `(1 . ,(append accum-pp pp)))
		   (t (dpp/dv (cdr pp) v (append accum-pp (cons (car pp) nil)))))))))

;;;
;;; MK-SQR-FREE: Given a univariate polynomial p, return its square-free part.
;;;  (Of course, we should never need count to reach 2!)
;;;

(defun mk-sqr-free (p)
  (let* ((out p)
	 (gcd 1)
	 (count 0)
	 (v (caadar p))
	 (var-name (nth v *vars-table*)))
    (fmt 8 "~%~%>> Reducing Polynomial to its Square-free Part:~%~%    P_{0} = ~A," (poly-print p))
    (while (progn (setq gcd (poly-univ-gcd out (dp/dv out v)))
		  (not (equal gcd '((1)))))
      (fmt 8 "~%    P_{~A} = P_{~A}/[gcd(P_{~A},dP_{~A}/d~A)] = P_{~A}/[~A] = " 
	   (1+ count) count count count var-name count (poly-print gcd))
      (setq count (1+ count))
      (setq out (car (poly-univ-/ out gcd)))
      (fmt 8 "~A.~%~%" (poly-print out)))
    out))

;;;
;;; STURM-CHAIN: Given a polynomial, p, univariate in v, return the Sturm Chain
;;; derived from p w.r.t. v.
;;;

(defun sturm-chain (p v)
  (let ((cur-dp/dv (dp/dv p v)))
    (append `(,p ,cur-dp/dv) (sturm-chain* p cur-dp/dv nil))))

(defun sturm-chain* (p1 p2 sc-accum)
  (let ((cur-rem (cdr (poly-univ-/ p1 p2))))
    (cond ((or (eq cur-rem 0) (eq cur-rem nil)) 
	   (reverse sc-accum))
	  (t (sturm-chain* p2 (poly-negate cur-rem) 
			   (cons (poly-negate cur-rem) sc-accum))))))

;;;
;;; SIGN-CHANGES: Given a sequence of rational numbers, S, calculate the number of
;;; sign changes (ignoring zeroes) that occur in S.
;;;

(defun sign-changes (S)
  (sign-changes* S (calc-sign (car S)) 0))

(defun sign-changes* (S c a)
  (cond ((endp S) a)
	(t (let ((cur-sign (calc-sign (car S))))
	     (cond ((or (= cur-sign 0)
			(= cur-sign c))
		    (sign-changes* (cdr S) c a))
		   (t (sign-changes* (cdr S) cur-sign 
				     (if (= c 0) a (1+ a)))))))))
	     
(defun calc-sign (r)
  (cond ((< r 0) -1)
	((> r 0) 1)
	(t 0)))

;;;
;;; POLY-UNIV-INTERVAL-REAL-ROOT-COUNT: Given a polynomial p, univariate in v, and two 
;;; rational numbers, a and b, compute the number of (unique) real roots of p there are in [a,b].
;;;

(defun poly-univ-interval-real-root-count (p a b &key p-sqr-free)
  (let ((v (caadar p))
	(sqr-free-p (if p-sqr-free p-sqr-free (mk-sqr-free p))))
    (cond ((> a b) 0)
	  ((= a b) (if (= (poly-univ-eval sqr-free-p a) 0) 1 0))
	  (t (let ((cur-sturm-chain (sturm-chain sqr-free-p v)))
	       (+ (if (= (poly-univ-eval sqr-free-p a) 0) 1 0) 
		  (- (sign-changes 
		      (mapcar #'(lambda (poly) (poly-univ-eval poly a)) cur-sturm-chain)) 
		     (sign-changes 
		      (mapcar #'(lambda (poly) (poly-univ-eval poly b)) cur-sturm-chain)))))))))

;;;
;;; CAUCHY-ROOT-BOUND: Given a univariate polynomial p in v, use the Cauchy root bound
;;;  formula to compute a rational interval containing all real roots of p.
;;;
;;; Bound:
;;;          p = a_k x^k + a_{k-1} x^{k-1} + ... + a_1 x^1 + a_0.
;;;
;;;  Let C(p)  = \sum_{0 <= i <= k} \frac{|a_i|}{|a_k|},
;;;
;;;  Then, p(r) = 0  ==> |r| in [-C(p), C(P)].
;;;  
;;; We return C(p).
;;;

(defun cauchy-root-bound (p)
  (fmt 8 "~%>> Preparing Cauchy root bound:~%")
  (let ((abs-a_k nil) (abs-coeff-lst nil))
    (dolist (m p)
      (when (equal abs-a_k nil) (setq abs-a_k (abs (car m))))
      (setq abs-coeff-lst (cons (abs (car m)) abs-coeff-lst)))
    (fmt 8 "~%    <|a_i|>: ~A,~%     |a_k|:  ~A.~%" 
	 abs-coeff-lst abs-a_k)
    (let ((up-c 
	   (reduce '+ (mapcar #'(lambda (x) (/ x abs-a_k)) abs-coeff-lst))))
      (fmt 8 "~%>> Result of Cauchy root bound:~%~%     P:    ~A,
     C(p): ~A,~%     So, p(r) = 0  ==>  r in [~A, ~A].~%~%"
	   (poly-print p) up-c (- 0 up-c) up-c)
      up-c)))

;;;
;;; NUM-REAL-ROOTS: Given a univariate polynomial p, return the total number of
;;;  real roots it has.
;;;

(defun num-real-roots (p)
  (let* ((sqr-free-p (mk-sqr-free p))
	 (b (cauchy-root-bound sqr-free-p)))
    (poly-univ-interval-real-root-count p (- 0 b) b :p-sqr-free sqr-free-p)))

;;;
;;;
;;; REAL-ROOT-ISOLATION: Given a univariate polynomial p, return a list of intervals
;;;  I_1, ..., I_k (pairwise disjoint) s.t. each I_i contains exactly one real root of p.
;;;  This list is exhaustive (p has exactly k real roots, multiplicity ignored).
;;;
;;; We return a list of elements which are either open intervals (as pairs) or 
;;;  single points.
;;;

(defun real-root-isolation (p)
  (let ((b (cauchy-root-bound p)))
    (real-root-isolation* p (- 0 b) b)))

(defun real-root-isolation* (p a b)
  (cond ((> a b) nil)
	(t (let ((n (poly-univ-interval-real-root-count p a b)))
	     (cond ((= n 0) nil)
		   ((= n 1) (cond ((= (poly-univ-eval p a) 0)
				   (list a))
				  ((= (poly-univ-eval p b) 0)
				   (list b))
				  (t (list (cons a b)))))
		   (t (let ((mid (/ (+ a b) 2)))
			(union (real-root-isolation* p a mid)
			       (real-root-isolation* p mid b)))))))))

;;;
;;; FLOAT-RRI: Given a real root isolation list as computed above,
;;;  map its entries to floats.  This is just for gaining intuition when
;;;  investigating root diagrams interactively.
;;;

(defun float-rri (rri)
  (let ((out nil))
    (dolist (r rri)
      (cond ((consp r) (setq out 
			     (cons (cons (float (car r))
					 (float (cdr r))) out)))
	    (t (setq out (cons (float r) out)))))
    out))

#|

 Some examples:

 (defparameter *p1* '( (2 . ((3 . 2) (2 . 7) (0 . 9)))  (3 . ((2 . 11)))))

 (poly-print *p1*)
"2x^9 z^7 u^2  +  3z^11"

(poly-print (dp/dv *p1* 2))
"14x^9 z^6 u^2  +  33z^10"

(poly-print (dp/dv *p1* 4))
"2x^9 z^7 u^2  +  3z^11"


(defparameter *f*
  '((1 . ((0 . 3))) (-2 . ((0 . 2))) (2 . ((0 . 1))) (8 . nil)))


(mapcar #'poly-print (sturm-chain *f* 0))
("3x^2  +  -4x  +  2" "4/9x  +  76/9" "1161")


(defparameter *p2*
  '( (1 . ((0 . 4))) (-5 . ((0 . 2))) (4)))

(poly-print *p2*)
"x^4  +  -5x^2  +  4"

(mapcar #'poly-print (sturm-chain *p2* 0))
("x^4  +  -5x^2  +  4" "4x^3  +  -10x" "5/2x^2  +  -4" "18/5x" "4")

(poly-univ-interval-real-root-count *p2* -2 2)
4

|#