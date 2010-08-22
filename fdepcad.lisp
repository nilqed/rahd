;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Full-dimensional extended partial cylindrical algebraic decomposition.
;;;
;;; (Explained in detail in my PhD dissertation).
;;;
;;;  Note: We support two projection operators -- 
;;;    (i) standard projection (e.g., Basu-Pollack-Roy),
;;;   (ii) Brown-McCallum projection (which is valid for f.d. lifting).
;;;
;;;  Certainly we expect (ii) to be almost always better in the f.d. case!
;;;
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         03-July-2010,
;;;            last updated on  21-August-2010.
;;;

;;;
;;; P-HASH-IN-V: Given a RAHD (algebraic rep) polynomial P, and a variable
;;;  id VAR-ID, construct a hash-table for P which is of the form:
;;;     KEY(i) |-> Coeff(X^i in P), 
;;;       with Coeff(_) in Q[*vars-table* \ {V}], where V is the variable
;;;        with var id VAR-ID.
;;;

(defun p-hash-in-v (p var-id)
  (let ((p-hash (make-hash-table :test 'eq)))
    (dolist (m p)
      (let ((m-coeff (car m))
	    (m-pp (cdr m)))
	(multiple-value-bind
	    (vp-in-v rst-pp)
	    (extract-vp-in-v m-pp var-id)
	  (let ((m-deg-in-v (if vp-in-v (cdr vp-in-v) 0)))
	    (let ((cur-deg-sym-coeff (gethash m-deg-in-v p-hash)))
	      (setf (gethash m-deg-in-v p-hash)
		    (poly+ `((,m-coeff . ,rst-pp)) cur-deg-sym-coeff)))))))
    p-hash))

;;;
;;; P-HASH-TO-P: Given a P-HASH for a polynomial with main variable given by
;;;  var-id, reconstuct P from the P-HASH.
;;;

(defun p-hash-to-p (p-hash var-id)
  (let ((out))
    (maphash #'(lambda (x y) 
		 (let ((vp-as-p `((1 . ((,var-id . ,x))))))
		   (setq out (poly+ (poly-mult vp-as-p y) out))))
	     p-hash)
    out))

;;;
;;; TRUNC: Given a polynomial P in prover notation and a var-id VAR-ID,
;;;   return a list of all truncations of P w.r.t. VAR-ID.
;;;

(defun trunc (p var-id)
  (let ((p-hash (p-hash-in-v p var-id)))
    (trunc-p-hash p-hash var-id)))

(defun trunc-p-hash (p-hash var-id)
  (let ((out))
    (loop for deg-bound being the hash-key of p-hash do
      (let ((deg-bound-trunc))
	(loop for cur-deg from 0 to deg-bound do
	      (let ((vp-as-p `((1 . ((,var-id . ,cur-deg))))))
		(setq deg-bound-trunc
		      (poly+ (poly-mult vp-as-p (gethash cur-deg p-hash))
			     deg-bound-trunc))))
	(setq out (union out (list deg-bound-trunc)))))
    out))

;;;
;;; TRUNC-SET: Given a list of polynomials and a var-id VAR-ID for the
;;;   main variable, return a list of all polynomials which arise in
;;;   computing all truncations of the polynomials in the input list.
;;;

(defun trunc-set (polys var-id)
  (let ((out nil))
    (dolist (p polys)
      (setq out (union out (trunc p var-id))))
    out))

;;;
;;; P-HASH-DEG: Given a P-HASH, compute the degree of
;;;  the polynomial (in an implicit VAR-ID) corresponding to P-HASH.
;;;
;;; If P-HASH corresponds to a poly w.r.t. VAR-ID which is identically 0,
;;;  then we break with an error.
;;;

(defun p-hash-deg (p-hash)
  (when (= (hash-table-count p-hash) 0)
    (break "Asked to compute degree of 0 polynomial hash"))
  (let ((deg 0))
    (loop for cur-deg being the hash-key of p-hash do
	  (setq deg (max deg cur-deg)))
    deg))

;;;
;;; SRES-SEQ-P-DP/DV: Given a polynomial P and a main variable VAR-ID,
;;;  compute the signed subresultant coefficient sequence:
;;;   [ sRes_j(P,dP/dV) ]_{j in 0 ... deg_{V}(R) - 2}, 
;;;     where V is the variable whose var-id is VAR-ID.
;;;
;;; P is given in algebraic notation.
;;;

(defun sres-seq-p-dp/dv (p var-id)
  (let ((dpoly/dv (dp/dv p var-id)))
    (when dpoly/dv
      (multiple-value-bind
	  (ssubres-prs ssubres-prs-coeffs)
	  (ssubres (poly-alg-rep-to-prover-rep p)
		   (poly-alg-rep-to-prover-rep dpoly/dv)
		   (nth var-id *vars-table*))
	(declare (ignore ssubres-prs))
	ssubres-prs-coeffs))))

;;;
;;; P-HASH-LCOEFF: Given a P-HASH of a polynomial w.r.t an implicit main 
;;;  variable, return the leading coefficient of the P-HASH, which is the 
;;;  leading coefficient of the original polynomial corresponding to the 
;;;  P-HASH w.r.t. the implicit VAR-ID.
;;;

(defun p-hash-lcoeff (p-hash)
  (let ((deg (p-hash-deg p-hash)))
    (gethash deg p-hash)))

;;;
;;; P-P-HASH-HAT: Given two polynomials, S and R, and their respective P-HASHes 
;;;  computed w.r.t. some var id VAR-ID, compute the `hat' of R, 
;;;  which is given as:
;;;                      L(S)R - L(R)S, where
;;;   L(P) is the leading coefficient of L w.r.t. the var id VAR-ID.
;;;

(defun p-p-hash-hat (s r s-hash r-hash)
  (poly- (poly-mult (p-hash-lcoeff s-hash) r) 
	 (poly-mult (p-hash-lcoeff r-hash) s)))

;;;
;;; Given a polynomial in algebraic rep and a main variable var-id, return
;;;  the leading coefficient of the polynomial w.r.t. var-id.
;;;
;;; Polynomials are given and returned in algebraic notation.

(defun lcoeff (p var-id)
  (let ((ph (p-hash-in-v p var-id)))
    (p-hash-lcoeff ph)))

(defun lcoeffs (ps var-id)
  (remove-duplicates
   (mapcar #'(lambda (p)
	       (lcoeff p var-id)) ps)
   :test 'equal))

;;;
;;; Given a list of polynomials and a main variable var-id, return a
;;;   list of discriminants of the polynomials in the list w.r.t.
;;;   the main variable.
;;;
;;; Polynomials are given and returned in algebraic notation.
;;;

(defun discrs (ps var-id)
  (remove-duplicates
   (mapcar #'(lambda (p)
	       (poly-prover-rep-to-alg-rep
		(poly-expand-expts
		(discriminant 
		 (poly-alg-rep-to-prover-rep p)
		 (nth var-id *vars-table*)))))
	   ps)
   :test 'equal))

;;;
;;; Given a list of polynomials and a main variable var-id, return a
;;;   list of all resultants between pairwise distinct polynomials in
;;;   the given list w.r.t. the main variable.
;;;

(defun ress (ps var-id)
  (let* ((n (length ps))
	 (a (make-array n :initial-contents ps))
	 (out))
    (loop for i from 0 to (1- n) do
      (loop for j from 0 to (1- n) do
        (when (not (= i j))
	  (let ((r (resultant (poly-alg-rep-to-prover-rep (aref a i))
			      (poly-alg-rep-to-prover-rep (aref a j))
			      (nth var-id *vars-table*))))
	    (setq out (cons  
		       (poly-prover-rep-to-alg-rep 
			(poly-expand-expts r)) out))))))
    (remove-duplicates out :test 'equal)))

;;;
;;; Clean rational constants: Given a list of polynomials, remove all rational
;;;   constants.
;;;

(defun clean-rcs (ps)
  (remove-if #'(lambda (p) (numberp (poly-alg-rep-to-prover-rep p))) ps))

;;;
;;; *** Full-dimensional CAD Projection Operator (mapped over all subdims) ***
;;;
;;; Given a set of polynomials P and a var id VAR-ID, compute a projection
;;;  factor set for P w.r.t. the variable order given, and do so using the
;;;  McCallum-Brown operator, which is valid for full-dimensional lifting.
;;;
;;; Polynomials are given in algebraic representation.
;;; Var-order is a list of var-ids w.r.t. VARS-LST.
;;;
;;; The result is an array A s.t. A[n] is the portion of the projection
;;;   factor set consisting of polynomials in n variables.
;;;
;;; Included: LCs, discrim's, resultants.
;;;

(defun fd-cad-project (ps var-order)
  (let ((sqr-free-base 
	 (clean-rcs 
	  (mapcar #'poly-prover-rep-to-alg-rep 
		  (sqr-free-dps (mapcar #'poly-alg-rep-to-prover-rep ps)))))
	(top-dim (length var-order)))
    (let ((cur-dim top-dim)
	  (cur-var nil)
	  (cur-ps nil)
	  (proj-fs-array (make-array top-dim)))
      (setf (aref proj-fs-array (1- top-dim)) sqr-free-base)
      
      (fmt 3 "~% CAD projection factor set component for dimension ~A:~%   ~A.~%~%"
	   cur-dim 
	   (mapcar #'poly-alg-rep-to-prover-rep sqr-free-base))

      (dolist (var-id var-order)
	(when (> cur-dim 1)
	  (setq cur-var (nth var-id *vars-table*))
	  (setq cur-ps (aref proj-fs-array (1- cur-dim)))
	  (fmt 9 "~% cur-ps(~A): ~A~%" 
	       cur-dim
	       (mapcar #'poly-alg-rep-to-prover-rep cur-ps))

	  (let ((lcs (lcoeffs cur-ps var-id))
		(ds (discrs cur-ps var-id))
		(rs (ress cur-ps var-id)))

	    (fmt 9 "~%...LCs, Ds, Rs computation completed for FD projection...~%")

	    (let ((cur-proj-fs
		   (mapcar #'poly-prover-rep-to-alg-rep
			   (sqr-free-dps
			    (mapcar #'poly-alg-rep-to-prover-rep
				    (clean-rcs
				     (union (union lcs ds :test 'equal) 
					    rs
					    :test 'equal)))))))

	      (fmt 3 "~% CAD projection factor set component for dimension ~A (eliminated ~A):~%   ~A.~%~%"
		   (1- cur-dim) 
		   cur-var
		   (mapcar #'poly-alg-rep-to-prover-rep cur-proj-fs))

	      (setq cur-dim (1- cur-dim))
	      (setf (aref proj-fs-array (1- cur-dim))
		    cur-proj-fs)))))
      proj-fs-array)))


;;; 
;;; *** Standard CAD Projection Operator ***
;;;
;;; Given a set of polynomials P and a var id VAR-ID, compute a projection
;;;  factor set for P w.r.t. the variable whose index is VAR-ID.
;;;
;;; Polynomials are given in algebraic representation.
;;;

(defun std-cad-project (ps var-id)
  (let ((proj-factor-set nil)
	(ps-p-hashes (make-hash-table :test 'equal)))
    (dolist (p ps)
      (let* ((p-hash (let ((known? (gethash p ps-p-hashes)))
		       (if known? known? 
			 (let ((p-hash* (p-hash-in-v p var-id)))
			   (setf (gethash p ps-p-hashes) p-hash*)
			   p-hash*))))
	     (deg-p (p-hash-deg p-hash)))
	(when (>= deg-p 2)
	  (let ((trunc-p (trunc-p-hash p-hash var-id)))
	    (dolist (r trunc-p)
	      (let ((sres-seq-r-dr/dv (sres-seq-p-dp/dv r var-id)))
		(setq proj-factor-set
		      (union proj-factor-set sres-seq-r-dr/dv))))))))
    (let ((trunc-set-ps (trunc-set ps var-id)))
      (dolist ((
    proj-factor-set))