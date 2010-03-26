;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A feasible decision method for the existential theory of real closed fields.
;;;
;;; ** Quantifier Elimination by Quadratic Virtual Term Substitution **
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         22-Nov-2009,
;;;            last updated on  26-Mar-2010.
;;;

;;;
;;; Form a square-root expression.
;;;

(defun sre-make (a b c d)
  (if (or (equal d 0) (and (numberp c) (< c 0)))
	  (break "VTS sqr-expr cannot be formed with c<0 or d=0")
    (make-array 4
		:initial-contents (list a b c d))))

;;;
;;; S+: If x,y are rationals, return x+y.
;;;  Otherwise, if x or y are symbolic, return `(+ ,x ,y).
;;;

(defun s+ (x y)
  (if (and (rationalp x) (rationalp y))
      (+ x y)
    `(+ ,x ,y)))

;;;
;;; S*: If x,y are rationals, return x*y.
;;;  Otherwise, if x or y are symbolic, return `(* ,x ,y).
;;;

(defun s* (x y)
  (if (and (rationalp x) (rationalp y))
      (* x y)
    `(* ,x ,y)))

;;;
;;; Add two square-root expressions with the same radicand (c).
;;;

(defun sre-add (x y)
  (let ((x_a (aref x 0)) (y_a (aref y 0))
	(x_b (aref x 1)) (y_b (aref y 1))
	(x_c (aref x 2)) (y_c (aref y 2))
	(x_d (aref x 3)) (y_d (aref y 3)))
    (if (not (equal x_c y_c))
	(break "VTS sqr-exprs can only be added with same radicand")
      (sre-make	(s+ (s* x_a y_d) (s* y_a x_d))
		(s+ (s* x_b y_d) (s* y_b x_d))
		x_c
		(s* x_d y_d)))))
;;;
;;; Multiply two square-root expressions with the same radicand (c).
;;;

(defun sre-mult (x y)
  (let ((x_a (aref x 0)) (y_a (aref y 0))
	(x_b (aref x 1)) (y_b (aref y 1))
	(x_c (aref x 2)) (y_c (aref y 2))
	(x_d (aref x 3)) (y_d (aref y 3)))
    (if (not (equal x_c y_c))
	(break "VTS sqr-exprs can only be multiplied with same radicand")
      (sre-make (s+ (s* x_a y_a) (s* x_c (s* y_b x_b)))
		(s+ (s* x_a y_b) (s* y_a x_b))
		x_c
		(s* x_d y_d)))))

;;;
;;; Multiply a square-root expression by a polynomial.
;;;

(defun sre-mult-poly (s k)
  (let ((s_a (aref s 0)) (s_b (aref s 1))
	(s_c (aref s 2)) (s_d (aref s 3)))
    (sre-make (s* k s_a)
	      (s* k s_b)
	      s_c
	      s_d)))

;;; 
;;; Efficient exponentiation for square-root expressions.
;;;
;;; Compute S^k where S is a square-root expression, using the
;;;  repeated squaring method.
;;;
;;; * Eventually, I should replace this with an iterative or
;;;    tail-recursive version.  But, this is just so clear.
;;;

(defun sre-expt (s k)
  (cond ((= k 0) (sre-make 1 0 0 1))
	((= k 1) s)
	((oddp k) (let ((o (sre-expt s (/ (1- k) 2))))
		    (sre-mult s (sre-mult o o))))
	(t (let ((o (sre-expt s (/ k 2))))
	     (sre-mult o o)))))

;;;
;;; Given a power-product in algebraic notation and a variable id,
;;;  return an MV of the form:
;;;   ( A B )  where A is the var-pow pair in the given var id,
;;;              and B is the list of the remaining var-pow pairs.
;;;

(defun extract-vp-in-v (pp var-id)
  (let ((a) (b) (pp* pp))
    (while (and (equal a nil) (not (endp pp*)))
      (let ((vp (car pp*)))
	(if (= (car vp) var-id)
	    (setq a vp)
	  (setq b (cons vp b)))
	(setq pp* (cdr pp*))))
    (values a (append (reverse b) pp*))))

;;;
;;; Substitute a square-root expression for a variable in a monomial.
;;;
;;; Observe that the coefficient K of a monomial M is represented
;;;  as a square-root expression in C as (K 0 C 1).
;;; Monomials are given in algebraic representation.
;;; A square-root expression is returned.
;;;

(defun sre-subst-monomial (s m var-id)
  (let ((m-coeff (car m))
	(m-pps (cdr m)))
    (multiple-value-bind 
	(target-vp rest-vps) 
	(extract-vp-in-v m-pps var-id)
      (if (not target-vp)
	  (sre-make (poly-alg-rep-to-prover-rep (list m))
		    0 (aref s 2) 1)
	(let ((target-vp-pow (cdr target-vp)))
	  (let ((sre-to-pow (sre-expt s target-vp-pow))
		(rest-p (poly-alg-rep-to-prover-rep 
			 (list (cons m-coeff rest-vps)))))
	    (sre-mult-poly sre-to-pow rest-p)))))))

;;;
;;; Substitute a square-root expression for a variable in a polynomial.
;;;
;;; Observe that the additive unit for SREs is (0 0 0 1).
;;; Polynomials are given in algebraic representation.
;;; A square-root expression is returned.
;;;

(defun sre-subst-poly (s p v)
  (let ((var-id (find-var v *vars-table* 0))
    	(out nil))
    (if (not var-id)
	p
      (dolist (m p)
	(setq out 
	      (if (not out)
		  (sre-subst-monomial s m var-id)
		(sre-add 
		 (sre-subst-monomial s m var-id)
		 out)))))
      out))

;;;
;;; Given a polynomial p in algebraic representation and a var-id,
;;;  compute the degree of *vars-table*[var-id] in p.
;;;

(defun poly-deg-in-v (p var-id)
  (let ((out nil)
	(ms p))
    (while (and ms (not out))
      (let* ((m (car ms))
	     (found? (assoc var-id (cdr m))))
	(when found? (setq out (cdr found?))))
      (setq ms (cdr ms)))
    (if out out 0)))

;;;
;;; Substitute a square-root expression within a single atomic
;;;  formula of the form (OP p 0).
;;;
;;; Atoms are given in prover representation.
;;;

(defun sre-subst-atom (s atom v)
  (let ((op (car atom))
	(x (cadr atom))
	(y (caddr atom)))
    (let* ((p (if (equal y 0) (poly-prover-rep-to-alg-rep x)
		(poly-prover-rep-to-alg-rep `(- ,x ,y))))
	   (deg-p-in-v (poly-deg-in-v p (find-var v *vars-table* 0)))
	   (sre-p* (sre-subst-poly s p v))
	   (delta (if (oddp deg-p-in-v) 1 0)))
      (let ((a (aref s 0)) (b (aref s 1)) (c (aref s 2)) (d (aref s 3))
	    (a* (aref sre-p* 0)) (b* (aref sre-p* 1)) 
	    (c* (aref sre-p* 2)) (d* (aref sre-p* 3)))
	(let ((d^delta (if (= delta 0) 1 d)))

	  ;;
	  ;; We now are in a position to take advantage of the
	  ;;  possibly nullity of the b component of sre s.
	  ;; If [sre(b)=0] then p(s/v) = (d*)^{-1}(a*)
	  ;;                           = (a* 0 c d*),
	  ;; and the substitution for OP is obtained as:
	  ;;   OP= : a* = 0,
	  ;;   OP<=: (a*)d^{delta} <= 0,
	  ;;   OP< : (a*)d^{delta} < 0.
	  ;;
	  
	  (cond ((equal b 0)
		 (case op
		   (=  `(= ,a* 0))
		   (<= `(<= (* ,a* ,d^delta) 0))
		   (<  `(< (* ,a* ,d^delta) 0))
		   (>  `(> (* ,a* ,d^delta) 0))
		   (>= `(>= (* ,a* ,d^delta) 0))))
		
		;;
		;; Otherwise, we must take care for arbitrary b.
		;;

		(t (case op
		     (= `(:and (<= (* ,a* ,b*) 0)
			       (= (- (* ,a* ,a*) (* (* ,b* ,b*) ,c)) 0)))
		     (<= `(:or (:and (<= (* ,a* ,d^delta) 0)
				     (>= (- (* ,a* ,a*) (* (* ,b* ,b*) ,c)) 0))
			       (:and (<= (* ,b* ,d^delta) 0)
				     (<= (- (* ,a* ,a*) (* (* ,b* ,b*) ,c)) 0)))

		     )))))))))