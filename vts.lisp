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
;;;            last updated on  02-April-2010.
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
    (if (or (equal x 0) (equal y 0))
	0
      `(* ,x ,y))))

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
  (let ((pre-op (car atom))
	(x (cadr atom))
	(y (caddr atom)))
    (let* ((op pre-op)
	   (pre-p (if (equal y 0) (poly-prover-rep-to-alg-rep x)
		    (poly-prover-rep-to-alg-rep `(- ,x ,y))))
	   (p (case pre-op
		(> (setq op '<)
		   (poly-negate pre-p))
		(>= (setq op '<=)
		    (poly-negate pre-p))
		(otherwise pre-p)))
	   (deg-p-in-v (poly-deg-in-v p (find-var v *vars-table* 0)))
	   (sre-p* (let ((sre-tmp (sre-subst-poly s p v)))
		     (if sre-tmp sre-tmp (sre-make 0 0 0 1))))
	   (delta (if (oddp deg-p-in-v) 1 0)))
      (let ((b (aref s 1)) (c (aref s 2)) (d (aref s 3))
	    (a* (aref sre-p* 0)) (b* (aref sre-p* 1)))
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
		   (=  `(= ,(simplify-term a* nil) 0))
		   (<= `(<= ,(simplify-term `(* ,a* ,d^delta) nil) 0))
		   (<  `(< ,(simplify-term `(* ,a* ,d^delta) nil) 0))))
		
		;;
		;; Otherwise, we must take care for arbitrary b.
		;;
		
		(t (case op
		     (= `(:and (<= ,(simplify-term `(* ,a* ,b*) nil) 0)
			       (= ,(simplify-term `(- (* ,a* ,a*) (* (* ,b* ,b*) ,c)) nil) 0)))
		     (<= `(:or (:and (<= ,(simplify-term `(* ,a* ,d^delta) nil) 0)
				     (>= ,(simplify-term `(- (* ,a* ,a*) (* (* ,b* ,b*) ,c)) nil) 0))
			       (:and (<= ,(simplify-term `(* ,b* ,d^delta) nil) 0)
				     (<= ,(simplify-term `(- (* ,a* ,a*) (* (* ,b* ,b*) ,c)) nil) 0))))
		     (< `(:or (:and (< ,(simplify-term `(* ,a* ,d^delta) nil) 0)
				    (> ,(simplify-term `(- (* ,a* ,a*) (* (* ,b* ,b*) ,c)) nil) 0))
			      (:and (<= ,(simplify-term `(* ,b* ,d^delta) nil) 0)
				    (:or (< ,(simplify-term `(* ,a* ,d^delta) nil) 0)
					 (< ,(simplify-term `(- (* ,a* ,a*) (* (* ,b* ,b*) ,c)) nil) 0)))))
		     (otherwise (break "OP error: ~A not supported for VTS." op))))))))))

;;;
;;; VTS-SIMPLIFIER: A simplifier for VTS formulae.
;;;   This simplifier takes a theory argument (thy) which consists
;;;   of a list of implicitly conjoined atomic formulas in the
;;;   method of Dolzmann's thesis.
;;;

(defun vts-simplifier (f thy)
  (vts-simplifier* f thy nil))

;; (defun vts-simplifier* (f thy acc)
;;   (cond ((endp f) acc)
;; 	(t (let 

;;;
;;; QE-QUAD-RESTRICTED: Eliminate a quantifier (exists v) from a 
;;;  quadratically restricted formula of the form
;;;         Psi := (av^2 + bv + c = 0   /\   Phi).
;;;   with quad-f = av^2 + bv + c.
;;;
;;; A,B,C,phi given in prover notation.  Right now, phi must be
;;;  an atomic formula.
;;;

(defun qe-quad-restricted (a b c v phi)
 
  ;;
  ;; If (a=0, b=0, c=0) then we break.
  ;;
  
  (if (and (equal (simplify-term a nil) 0) 
	   (equal (simplify-term b nil) 0) 
	   (equal (simplify-term c nil) 0))
      (break "QE-QUAD-RESTRICTED requires (a!=0 or b!=0 or c!=0)")
    
    ;;
    ;; Otherwise, we eliminate v!
    ;; If we see explicitly that (a!=0 \/ b!=0 \/ c!=0) then we 
    ;;  may skip expressing the degenerate (0=0 /\ Phi) case in QE out.
    ;;

    (let ((explicit-non-degenerate
	   (or (and (numberp a) (not (= a 0)))
	       (and (numberp b) (not (= b 0)))
	       (and (numberp c) (not (= c 0)))))
	  
	  (pre-out `(:or (:and (= ,a 0) (not (= ,b 0))
			       ,(sre-subst-atom (sre-make 0 0 c `(* -1 ,b)) phi v))
			 (:and (not (= ,a 0)) (>= (- (* ,b ,b) (* 4 (* ,a ,c))) 0)
			       ,(sre-subst-atom (sre-make `(- 0 ,b)
							  1
							  `(- (* ,b ,b) (* 4 (* ,a ,c)))
							  `(* 2 ,a)) phi v))
			 ,(sre-subst-atom (sre-make `(- 0 ,b)
						    -1
						    `(- (* ,b ,b) (* 4 (* ,a ,c)))
						    `(* 2 ,a))
					  phi v))))

	  (if explicit-non-degenerate 
	      pre-out
	    `(:or (:meta-assumption (:or (not (= ,a 0)) (not (= ,b 0)) (not (= ,c 0)))) ,@(cdr pre-out))))))