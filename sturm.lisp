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
;;;            last updated on  23-August-2010.
;;;

(in-package RAHD)

;;;
;;; Notes: [26-May-2010]: Added caching of Sturm sequences and square-free
;;;                        reductions.
;;;

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
;;; Now uses global square-free poly cache.
;;;

(defun mk-sqr-free (p)
  (multiple-value-bind
      (sqr-free-hash-val sqr-free-hash-exists?)
      (gethash p *sqr-free-cache*)
    (if sqr-free-hash-exists?
	sqr-free-hash-val 
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
	(setf (gethash p *sqr-free-cache*) out)
	out))))

;;;
;;; STURM-CHAIN: Given a polynomial, p, univariate in v, return the Sturm Chain
;;; derived from p w.r.t. v.
;;;
;;; Now uses global Sturm chain cache.
;;;

(defun sturm-chain (p v)
  (multiple-value-bind 
      (sturm-seq-hash-val sturm-seq-hash-exists?)
      (gethash p *sturm-seq-cache*)
    (if sturm-seq-hash-exists?
	sturm-seq-hash-val
      (let* ((cur-dp/dv (dp/dv p v))
	     (chain (append `(,p ,cur-dp/dv) (sturm-chain* p cur-dp/dv nil))))
	(setf (gethash p *sturm-seq-cache*) chain)
	chain))))

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
;;; Note: If p-sqr-free? is true, then we assume p is already square-free.
;;;

(defun poly-univ-interval-real-root-count (p a b &key p-sqr-free?)
  (let ((v (caadar p))
	(sqr-free-p (if p-sqr-free? p (mk-sqr-free p))))
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
;;;  Then, p(r) = 0  ==> r in [-C(p), C(P)].
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
;;; MINIMIZE-CAUCHY-BOUND: Given a Cauchy root bound, minimize it by the
;;;  highest power of two s.t. the resulting bound still contains all roots.
;;;
;;; We assume p is given square-free.
;;;

(defun minimize-cauchy-bound (p b base)
  (minimize-cauchy-bound* 
   p 
   b 
   (poly-univ-interval-real-root-count 
    p 
    (- 0 b) 
    b
    :p-sqr-free? t)
   base))

(defun minimize-cauchy-bound* (p b k base)
  (let* ((b* (/ b base))
	 (k* (poly-univ-interval-real-root-count 
	      p 
	      (- 0 b*)
	      b
	      :p-sqr-free? t)))
    (cond ((= k* k) 
	   (fmt 8 ".")
	   (minimize-cauchy-bound* p b* k base))
	  ((< k* k) b))))

;;;
;;; Compute a minimal root bound by minimizing Cauchy bound w.r.t. 2^{-k} sequence.
;;;

(defun min-root-bound (p &key p-sqr-free? min-base)
  (let* ((p* (if p-sqr-free? p (mk-sqr-free p)))
	 (b (cauchy-root-bound p*))
	 (mb (or min-base 2))
	 (b* (progn 
	       (fmt 8 "~%>> Minimizing Cauchy root bound (kth `.' means ~A^k pruned):~%~%    " mb)
	       (minimize-cauchy-bound p* b mb))))
    (fmt 8 "~%    Revised root bound: [~A, ~A].~%" (- 0 b*) b*)
    b*))

;;;
;;; NUM-REAL-ROOTS: Given a univariate polynomial p, return the total number of
;;;  real roots it has.
;;;

(defun num-real-roots (p)
  (let* ((sqr-free-p (mk-sqr-free p))
	 (b (cauchy-root-bound sqr-free-p)))
    (poly-univ-interval-real-root-count sqr-free-p (- 0 b) b :p-sqr-free? t)))

;;;
;;; SORT-RD: Sort a root diagram.  We assume all members are disjoint.
;;;

(defun rd-<= (rx ry)
  (cond ((and (numberp rx) (numberp ry))
	 (<= rx ry))
	((and (numberp rx) (consp ry))
	 (<= rx (car ry)))
	((and (consp rx) (numberp ry))
	 (<= (cdr rx) ry))
	((and (consp rx) (consp ry))
	 (<= (car rx) (car ry)))))

(defun sort-rd (rd)
  (sort rd #'rd-<=))

;;;
;;;
;;; REAL-ROOT-ISOLATION: Given a univariate polynomial p, return a list of intervals
;;;  I_1, ..., I_k (pairwise disjoint) s.t. each I_i contains exactly one real root of p.
;;;  This list is exhaustive (p has exactly k real roots, multiplicity ignored).
;;;
;;; We return a list of elements which are either open intervals (as pairs) or 
;;;  single points.
;;;
;;; Epsilon is a rational W s.t. the interval given for each real root
;;;  must have width <= W.
;;;


(defun rri (p &key use-min-bound? min-base epsilon)
  (real-root-isolation 
   p 
   :use-min-bound? use-min-bound? 
   :min-base min-base
   :epsilon epsilon))

(defun real-root-isolation (p &key use-min-bound? min-base epsilon)
  (let* ((sqr-free-p (mk-sqr-free p))
	 (b (if use-min-bound?
		(min-root-bound sqr-free-p :p-sqr-free? t :min-base min-base)
	      (cauchy-root-bound sqr-free-p))))
    (fmt 8 "~%>> Isolating roots:~%~%")
    (let ((rri (real-root-isolation* sqr-free-p (- 0 b) b 0 :epsilon epsilon)))
      (fmt 8 "~%")
      rri)))

(defun real-root-isolation* (p a b d &key epsilon)
  (cond ((> a b) nil)
	(t (let ((n (poly-univ-interval-real-root-count p a b :p-sqr-free? t)))
	     (cond ((= n 0) nil)
		   ((= n 1) (fmt 8 "    .. Root isolated at depth ~A~%" d)
		    (cond ((= (poly-univ-eval p a) 0)
			   (list a))
			  ((= (poly-univ-eval p b) 0)
			   (list b))
			  (t (cond 
			      (epsilon (let ((tightened-root (tighten-root p a b epsilon)))
					 (fmt 8 "~%~%")
					 tightened-root))
			      (t (list (cons a b)))))))
		   (t (let ((mid (/ (+ a b) 2)))
			(union (real-root-isolation* p a mid (+ d 1) :epsilon epsilon)
			       (real-root-isolation* p mid b (+ d 1) :epsilon epsilon)))))))))

;;;
;;; TIGHTEN-ROOT: Given a root of a polynomial p as given by a rational interval,
;;;  tighten the interval so that its width is <= a given W.
;;;

(defun tighten-root (p a b w)
  (fmt 8 "~%       ..: Tightening root (~A . ~A) to epsilon width ~A (cur: ~A)" a b w (abs (- a b)))
  (cond ((<= (abs (- a b)) w) (list (cons a b)))
	((= (poly-univ-eval p a) 0) (list a))
	((= (poly-univ-eval p b) 0) (list b))
	(t (let* ((mid (/ (+ a b) 2))
		  (root-l? (= 1 (poly-univ-interval-real-root-count p a mid :p-sqr-free? t)))
		  (root-r? (= 1 (poly-univ-interval-real-root-count p mid b :p-sqr-free? t))))
	     (cond ((and root-l? root-r?) (list mid))
		   (root-l? (tighten-root p a mid w))
		   (root-r? (tighten-root p mid b w)))))))

;;;
;;; FLOAT-RRI: Given a real root isolation list as computed above,
;;;  map its entries to floats.  This is just for gaining intuition when
;;;  investigating root diagrams interactively (I find it easier to
;;;  read floats so as to get a picture of the placement of roots than
;;;  I do reading rationals with large numerators/denominators).
;;;

(defun float-rri (rri)
  (let ((out nil))
    (dolist (r rri)
      (cond ((consp r) (setq out 
			     (cons (cons (float (car r))
					 (float (cdr r))) out)))
	    (t (setq out (cons (float r) out)))))
    out))

(defun r-ub (r)
  (cond ((numberp r) r)
	((consp r) (cdr r))))

(defun r-lb (r)
  (cond ((numberp r) r)
	((consp r) (car r))))

;;;
;;; RRI-PS: Isolate the real roots of a list of univariate polynomials.
;;;  We must iterate on refining the roots until their containing intervals
;;;  are sufficiently disjoint so as to be able to select a sample point
;;;  between each of them.
;;;
;;; We assume the set of polynomials is square-free and pair-wise 
;;;  relatively prime.
;;;
;;; We call a list of pairs a `tagged root family' if it is of the form
;;;   (p . R) s.t. R is a list of either open intervals or points
;;;   corresponding to a root diagram for p.
;;;

;(defun rri-ps (ps)
;  (let ((cur-rf) (cur-epsilon 1/10))
;    (dolist (p ps)
;      (let ((tagged-new-roots (cons p (rri p :epsilon cur-epsilon))))
;	(setq cur-rf (append tagged-new-roots cur-rf))))
;    (if (rf-tight? cur-rf)
;	cur-rf
;      (while (not (rf-tight? cur-rf))
;	(
    
;;;
;;; RRI-TIGHT-ENOUGH?: Is a root diagram tight enough to select a point
;;;   between each of the roots it isolates?
;;;

(defun rri-tight-enough? (rri)
  (let ((rri* (copy-list rri)))
    (cond ((<= (length rri*) 1) t)
	  (t (setq rri* (sort-rd rri*))
	     (let ((tight? t))
	       (loop for i from 0 to (- (length rri*) 2) do
		 (when (>= (r-ub (car rri*))
			   (r-lb (cadr rri*)))
		   (setq tight? nil))
		 (setq rri* (cdr rri*)))
	       tight?)))))

;;;
;;; RRI-PS-MULT: Compute the list of real roots of a family of polynomials
;;;  (univariate) by first taking their product and then isolating the
;;;  roots of that product polynomial.
;;;
;;; Note: We should see if any of the factors are linear (happens often!),
;;;  and if so, solve for their single real root, keep it, and then remove
;;;  that factor and divide all remaining factors by it before performing
;;;  the multiplication.
;;;

(defun rri-ps-mult* (ps &key epsilon)
  (let ((prod '((1)))
	(linear-roots)
	(linear-factors))
    (dolist (p ps)
      (let* ((p* (poly-alg-rep-to-prover-rep p))
	     (derived-eq `(= ,p* 0))
	     (lin-oriented (orient-partial-lineq derived-eq))
	     (derived-root (when lin-oriented (caddr lin-oriented))))
	(cond (lin-oriented
	       (fmt 4 "~%    Avoiding including linear factor in product:~%     p:  ~A,~%     r: ~A.~%"
		    p* derived-root)
	       (setq linear-roots (cons derived-root linear-roots))
	       (setq linear-factors (cons p linear-factors)))
	      (t (setq prod (poly-mult p prod))))))
    (union linear-roots 
	   (when (> (length ps) (length linear-factors))
	     (setq prod (mk-sqr-free prod))
	     (dolist (f linear-factors)
	       (let ((div-result (poly-univ-/ prod f)))
		 (when (not (cdr div-result))
		   (setq prod (car div-result)))))
	     (when (not (numberp (poly-alg-rep-to-prover-rep prod)))
	       (rri prod :epsilon epsilon))))))

(defun rri-ps-mult (ps &key epsilon)
  (let ((done?) (cur-epsilon epsilon) (cur-rri))
    (loop until done? do
      (setq cur-rri (rri-ps-mult* ps :epsilon cur-epsilon))
      (cond ((not (rri-tight-enough? cur-rri))
	     (setq cur-epsilon 
		   (/ (or cur-epsilon 1) 2)))
	    (t (setq done? t))))
    cur-rri))

;;;
;;; RRI-RATIONAL-SAMPLE-PTS: Given a list of root intervals (a root diagram), 
;;;  return a list of rational sample points in between all roots (and <,> 
;;;  than all roots).
;;;

(defun rri-rational-sample-pts (rd)
  (cond ((not rd) nil)
	(t 
	 (let* ((rd-count (length rd))
		(sorted-rd-array 
		 (make-array rd-count :initial-contents (sort-rd rd)))
		(sample-pts-array
		 (make-array (1+ rd-count))))
	   (loop for i from 0 to rd-count do
		 (cond ((= i 0)
			(setf (aref sample-pts-array 0) 
			      (1- (r-lb (aref sorted-rd-array 0)))))
		       ((= i rd-count)
			(setf (aref sample-pts-array rd-count) 
			      (1+ (r-ub (aref sorted-rd-array (1- rd-count))))))
		       (t (let ((si (aref sorted-rd-array (1- i)))
				(si+1 (aref sorted-rd-array i)))
			    (setf (aref sample-pts-array i)
				  (/ (+ (r-ub si) (r-lb si+1)) 2))))))
	   sample-pts-array))))

;;;
;;; PS-RATIONAL-SAMPLE-PTS: Given a list of univariate polynomials, return
;;;  a list of rational sample points extracted from a root diagram for
;;;  them.
;;;

(defun ps-rational-sample-pts (ps &key epsilon)
  (if (or (not ps) (ps-numbers-only ps))
      '(0)
    (let ((rd (rri-ps-mult ps :epsilon epsilon)))
      (rri-rational-sample-pts rd))))

(defun ps-numbers-only (ps)
  (every #'p-alg-number ps))

(defun p-alg-number (p)
  (or (equal p nil)
      (and (consp p)
	   (consp (car p))
	   (equal (length (car p)) 1)
	   (numberp (caar p)))))