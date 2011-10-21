;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Abstract Partial Cylindrical Algebraic Decomposition,
;;;   the full-dimensional case.
;;;
;;; (Explained in my PhD dissertation).
;;;
;;;  Note: We support one projection operator -- 
;;;    o Brown-McCallum projection (which is valid for f.d. lifting).
;;;
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Research Intern, Microsoft Research
;;; Visiting Researcher, INRIA/IRISA
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         03-July-2010,
;;;            last updated on  08-April-2011.
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
;;; VAR-ORDER is a list of var-ids w.r.t. VARS-LST -- we eliminate the
;;;   variables in the order given in VAR-ORDER.  Intuitively, this
;;;   means VAR-ORDER is the reverse of the list of variables sequentially
;;;   appearing in the existential quantification of the input problem
;;;   when read from left to right.
;;;
;;; The result is an array A s.t. A[n] is the portion of the projection
;;;   factor set consisting of polynomials in n variables.  By virtue of
;;;   the Brown-McCallum projection used, A[n] may fail to contain all
;;;   n variables.  We take care of this during lifting/stack construction.
;;;
;;; Included: LCs, discrim's, resultants.
;;;
;;; Keyword factor? determines if we should pre-process with factorisation.
;;;  This is done within sqr-free-dps.
;;;

(defun fd-cad-project (ps var-order &key factor?)
  (let ((hash-key (cons var-order ps)))
    (multiple-value-bind 
	(cached-pfs pfs-present?)
	(gethash hash-key *cad-pfs-cache*)
      (cond (pfs-present? 
	     (fmt 2 "~%   Projection factor set found in PFS cache! ~%")
	     cached-pfs)
	    (t (let ((pfs (fd-cad-project* ps var-order :factor? factor?)))
		 (setf (gethash hash-key *cad-pfs-cache*) pfs)
		 pfs))))))

(defun fd-cad-project* (ps var-order &key factor?)
  (let ((sqr-free-base 
	 (clean-rcs 
	  (mapcar #'(lambda (p)
		      (poly-prover-rep-to-alg-rep 
		       (poly-expand-expts p)))
		  (sqr-free-dps 
		   (mapcar #'poly-alg-rep-to-prover-rep ps)
		   :factor? factor?))))
	(top-dim (length var-order)))
    (let ((cur-dim top-dim)
	  (cur-var nil)
	  (cur-ps nil)
	  (proj-fs-array (make-array top-dim)))
      (setf (aref proj-fs-array (1- top-dim)) sqr-free-base)
      
      (fmt 2 "~%   cad pfs component for dimension ~A:~%    ~A.~%"
	   cur-dim 
	   (mapcar #'poly-alg-rep-to-prover-rep sqr-free-base))

      (dolist (var-id var-order)
	(when (> cur-dim 1)
	  (setq cur-var (nth var-id *vars-table*))
	  (setq cur-ps (aref proj-fs-array (1- cur-dim)))
	  (fmt 9 "~%   cur-ps(~A): ~A~%" 
	       cur-dim
	       (mapcar #'poly-alg-rep-to-prover-rep cur-ps))

	  (let ((lcs (lcoeffs cur-ps var-id))
		(ds (discrs cur-ps var-id))
		(rs (ress cur-ps var-id)))

	    (fmt 9 "~%     ...LCs, Ds, Rs computation completed for FD projection...~%")

	    (let ((cur-proj-fs
		   (mapcar #'(lambda (p) 
			       (poly-prover-rep-to-alg-rep
				(poly-expand-expts p)))
			   (sqr-free-dps
			    (mapcar #'poly-alg-rep-to-prover-rep
				    (clean-rcs
				     (union (union lcs ds :test 'equal) 
					    rs
					    :test 'equal)))))))

	      (fmt 2 "~%   cad pfs component for (R^~A) (eliminated ~A):~%    ~A.~%"
		   (1- cur-dim) 
		   cur-var
		   (mapcar #'poly-alg-rep-to-prover-rep cur-proj-fs))

	      (setq cur-dim (1- cur-dim))
	      (setf (aref proj-fs-array (1- cur-dim))
		    cur-proj-fs)))))
      proj-fs-array)))

;;;
;;; SPT-SUBST: Given a set of polynomials and a list of n variables and
;;;  an n-dimensional sample point, substitute the components of the 
;;;  sample point for the variables in the order given.
;;;

(defun spt-subst (ps pt vars)
  (when (not (equal (length pt) (length vars)))
    (break "cad subst error: sample point of wrong dimension"))
  (let ((out-ps ps) (vs vars))
    (dolist (c pt)
      (let ((cur-var (car vs)))
	(setq out-ps (subst c cur-var out-ps)))
      (setq vs (cdr vs)))
    (remove-duplicates out-ps :test 'equal)))

(defun spts-subst (ps pts vars)
  (mapcar #'(lambda (pt) 
	      (spt-subst ps pt vars))
	  pts))

(defun spts-subst-alg (ps pts vars)
  (let ((ps* (mapcar #'poly-alg-rep-to-prover-rep ps))
	(vs* (mapcar #'(lambda (i) (nth i *vars-table*)) vars)))
    (mapcar #'(lambda (ps) 
		(mapcar #'poly-prover-rep-to-alg-rep ps))
	    (spts-subst ps* pts vs*))))

;;;
;;; INSTANTIATE-CASE: Given a case and a list of n variables and an
;;;  n-dimensional sample point, instantiate the case upon the point
;;;  w.r.t. the given variable ordering.
;;;

(defun instantiate-case (c pt vars)
  (when (not (= (length pt) (length vars)))
    (break "instantiate-case: dimensional mismatch."))
  (dolist (q pt)
    (setq c (subst q (car vars) c))
    (setq vars (cdr vars)))
  c)

;;;
;;; DIRECT-EXCLUDE-CELL?: Given a case and a list of variable bindings
;;;  corresponding to a cell sample point (given as a list of variables
;;;  and a list of rationals in the form that SPST-SUBST accepts), see
;;;  if any conjuncts in the case are falsified by the sample point.
;;;  If so, then we need not lift over it and can short circuit the
;;;  corresponding stack construction.
;;;

(defun direct-exclude-cell? (c pt vars)
  (let* ((partially-instantiated-case
	  (instantiate-case c pt vars))
	 (simplified-pic
	  (simplify-ground-lits partially-instantiated-case)))
    (member nil simplified-pic)))

;;;
;;; DIRECT-EXCLUDE-CELLS: Given a list of sample points, remove those
;;;  which lead to an unsatisfied input formula.
;;;

(defun direct-exclude-cells (c pts vars)
  (remove-if #'(lambda (cell-sample-pt)
		 (direct-exclude-cell? c cell-sample-pt vars))
	     pts))

;;;
;;; Basic AP-CAD machinery:
;;;

(defun exec-covering-width-fcn (css pts)
  (let ((cell-selection-fcn (car css)) 
	(covering-width-fcn (cdr css)))
    (declare (ignorable cell-selection-fcn))
    (funcall covering-width-fcn pts)))

(defun exec-cell-selection-strategy-step-i (css i pts)
  (let ((cell-selection-fcn (car css))
	(covering-width-fcn (cdr css)))
    (declare (ignorable covering-width-fcn))
    (funcall cell-selection-fcn pts i)))

(defun exec-formula-construction-fcn (formula-construction-fcn phi pts vars)
  (funcall formula-construction-fcn phi pts vars))

(defun exec-proof-proc (formula rcf-strategy)
  (try-to-prove 
   :goal-key 'ap-cad-lifting
   :formula (mapcar #'list formula)
   :strategy rcf-strategy 
   :recursive? t))

;;;
;;; PROCESS-CELLS-BY-STAGE: Given an AP-CAD stage, apply it to a collection
;;;  of i-dimensional sample points.
;;;
;;; We take as input:
;;;  - a collection of i-dimensional sample points together with a listing
;;;    of the variables they correspond to,
;;;  - the top-level formula, which is a conjunctive case (C),
;;;  - an AP-CAD stage, which contains:
;;;        - a cell selection strategy,
;;;        - a formula construction function (FCF),
;;;        - a proof strategy (PRFSTRAT).
;;;
;;; We return a multiple-values form:
;;;   (remaining cells, sat-point-found?).
;;;

(defun lex-order< (v0 v1)
  (cond ((and (numberp v0)
	      (numberp v1)) (< v0 v1))
	((and (consp v0)
	      (consp v1))
	 (or (lex-order< (car v0) (car v1))
	     (lex-order< (cdr v0) (cdr v1))))))

(defun process-cells-by-stage (pts vars phi stage)
  (let ((cell-selection-strategy (car stage))
	(formula-construction-fcn (cadr stage))
	(rcf-proof-strategy (cddr stage)))
      stage
    (let ((U (exec-covering-width-fcn cell-selection-strategy pts))
	  (j 1)
	  (sample-pts (sort pts #'lex-order<)))
      (loop while (<= j U) do
	    (let ((selected-pts (exec-cell-selection-strategy-step-i 
				 cell-selection-strategy
				 j
				 sample-pts)))
	      (if selected-pts
		  (let ((rcf-result
			 (exec-proof-proc 
			  (exec-formula-construction-fcn 
			   formula-construction-fcn
			   phi
			   selected-pts
			   vars)
			  rcf-proof-strategy))
			(sample-pts*))
		    
		    (cond
		     ((eq rcf-result ':SAT)
		      (return ':SAT))
		     ((and (consp rcf-result)
			   (eq (car rcf-result) ':SAT)
			   (return ':SAT))) ; eventually return model here
		     ((eq rcf-result ':UNSAT)
		      (setq sample-pts* (sort (set-difference sample-pts selected-pts) #'lex-order<)))
		     (t (setq sample-pts* sample-pts)))
		    
		    (cond ((eq sample-pts* nil) 
			   (setq sample-pts nil)
			   (return nil))
			  ((equal (length sample-pts*) (length sample-pts))
			   (setq j (1+ j)))
			  ((< (length sample-pts*) (length sample-pts))
			   (setq sample-pts sample-pts*)
			   (setq U (exec-covering-width-fcn cell-selection-strategy sample-pts))
			   (setq j 1))))
		(setq j (1+ j)))))
      sample-pts)))

;;;
;;; Given a cell selection function, its covering width function,
;;;  a formula construction function and an RCF proof procedure
;;;  expressed as a RAHD strategy, make the corresponding AP-CAD
;;;  stage object.
;;;

(defun make-stage (csf cwf fcf rps)
  (cons (cons csf cwf)
	(cons fcf rps)))

;;;
;;; A few example stages.
;;;

(defun csf0 (pts i)
  (list (nth (1- i) pts)))

(defun cwf0 (pts)
  (length pts))

(defun fcf0 (phi pts vars)
  phi)
  
(defparameter *stage0*
  (make-stage #'csf0
	      #'cwf0
	      #'fcf0
	      '(run stable-simp)))

(defun theatre0 (n)
  (declare (ignore n))
  *stage0*)

;;;;
; A stage for divide-and-conquer interval analysis.
;;;;

;
; If a list is even, we give its first and second halves.
; If it is odd, then the extra item goes in the first `half'.
;

(defun first-half (l)
  (let ((len (length l)))
    (if (evenp len)
	(subseq l 0 (/ len 2))
      (subseq l 0 (+ (/ (- len 1) 2) 1)))))

(defun second-half (l)
  (let ((len (length l)))
    (if (evenp len)
	(subseq l (/ len 2))
      (subseq l (/ (+ 1 len) 2)))))

(defun div-conq (l i)
  (cond ((<= i 1) l)
	((evenp i) (first-half (div-conq l (/ i 2))))
	((oddp i) (second-half (div-conq l (/ (- i 1) 2))))))

(defun proj-pts (pts idx)
  (mapcar (lambda (p) (nth idx p)) pts))

(defun interval-fcf (phi pts vars)
  (let ((vs vars) (idx 0) (new-conjs))
    (dolist (v vs)
      (let ((v-pts (proj-pts pts idx)))
	(let ((v-pts-min (apply #'min v-pts))
	      (v-pts-max (apply #'max v-pts)))
	  (setq new-conjs
		(cons `(>= ,v ,v-pts-min)
		      (cons `(<= ,v ,v-pts-max)
			    new-conjs)))))
      (setq idx (1+ idx)))
    (append new-conjs phi)))
    
(defparameter *stage-interval-3* 
  (make-stage #'div-conq 
	      (lambda (i) (declare (ignore i)) 3) 
	      #'interval-fcf
	      '(THEN (APPLY SIMP-ZRHS)
		     (THEN (RUN STABLE-SIMP)
			   (THEN (APPLY SATUR-LIN) (APPLY INTERVAL-CP :MAX-CONTRACTIONS 30))))))

(defparameter *stage-tiwari* 
  (make-stage #'div-conq 
	      (lambda (i) (declare (ignore i)) 3) 
	      #'interval-fcf
	      '(THEN (APPLY SIMP-ZRHS)
		     (THEN (RUN STABLE-SIMP)
			   (THEN (APPLY SATUR-LIN) (APPLY BOUNDED-GBRNI))))))


(defun interval-theatre (n)
  (declare (ignore n))
  *stage-interval-3*)

(defun tiwari-theatre (n)
  (declare (ignore n))
  *stage-tiwari*)


#|
(apcad-fd-on-case (mapcar #'car (expand-formula '(((>= A 0)) ((>= B 0)) ((>= C 0)) ((>= D 0)) ((<= A 1)) ((<= B 1))
    ((<= C 1)) ((<= D 1))
    ((< (+ (* (- 1 (* A A B B)) (- 1 (* C D)) (- (* A D) (* B C))
              (- (* A D) (* B C)))
           (* (* 2 A B) (- (* C D) (* A B)) (- 1 (* A B)) (- C D)
              (- C D))
           (* (- (* A A B B) (* C C D D)) (- 1 (* C D)) (- A B)
              (- A B)))
        0)))))  #'interval-theatre)
|#

;;;
;;; APCAD-FD: Full-dimensional Apstract Partial CAD.
;;; We return an array of n-dimensional sample points.
;;;

(defun apcad-fd (ps var-order theatre &key epsilon formula factor? theatre-only?)
  (fmt 2 "~% [cad: Computing projection factor set (pfs)]")
  (let ((projfs (fd-cad-project ps var-order :factor? factor?))
	(lift-vars (reverse var-order))
	(lower-vars) (latest-pts) (short-circuit?))
    (fmt 2 "~% [cad: Beginning full-dimensional lifting]")
    (loop for d from 0 to (1- (length lift-vars)) 
	  while (not short-circuit?) do
      (let ((cur-var (car lift-vars))
	    (cur-pfs (aref projfs d)))
	(cond ((= d 0)
	       (fmt 2 "~%   Computing base phase (R^1):")
	       (setq latest-pts
		     (mapcar #'list 
			     (coerce 
			      (ps-rational-sample-pts cur-pfs :epsilon epsilon)
			      'list)))
	       (fmt 1.5 "~%    ~A base rational sample points isolated: ~A.~%" 
		    (length latest-pts) latest-pts))
	      (t (fmt 2 "~%   Computing lifting from (R^~A) to (R^~A):~%" d (1+ d))
		 (fmt 1.5 "    Substituting ~A sample points in (R^~A) into (R^~A) pfs: ~%"
		      (length latest-pts) d (1+ d))
		 (fmt 2.5 "     pfs:  ~A,~%" (mapcar #'poly-alg-rep-to-prover-rep
						 cur-pfs))
		 (fmt 2.5 "     pts:  ~A,~%" latest-pts)
		 (fmt 2.5 "     lvs:  ~A.~%" (mapcar #'(lambda (i) 
						    (nth i *vars-table*)) 
						lower-vars))
		 (let ((new-pfs-instances
			(mapcar #'clean-rcs 
				(spts-subst-alg cur-pfs latest-pts lower-vars))))
		   (fmt 2.5 "     npfs: ~A.~%" 
			(mapcar #'(lambda (ps) 
				    (mapcar #'poly-alg-rep-to-prover-rep ps))
				new-pfs-instances))
		   (fmt 2 "~%    Isolating roots and sample points of induced univariate families: ~%")
		   (let ((new-latest-pts) (cur-instance 0))
		     (dolist (pfs-instance new-pfs-instances)
		       (let ((new-roots 
			      (coerce (ps-rational-sample-pts pfs-instance :epsilon epsilon) 'list))
			     (parent-sample-pt (nth cur-instance latest-pts)))
			 (fmt 2.5 "     upts: ~A.~%" new-roots)
			 (let ((hd-sample-pts
				(mapcar #'(lambda (r) (cons r parent-sample-pt)) new-roots)))
			   (fmt 2.5 "     nhds: ~A.~%" hd-sample-pts)
			   (setq new-latest-pts (append hd-sample-pts new-latest-pts))))
		       (setq cur-instance (1+ cur-instance)))
		     (setq latest-pts new-latest-pts)))))
	(setq lower-vars (cons cur-var lower-vars)))

      ;;
      ;; Direct partial CAD check: Remove the new sample points which lead to direct
      ;;  inconsistency, if formula (conjunctive case) is given.
      ;;

      (when (and formula (cdr lift-vars))

	(let ((num-cells-before (length latest-pts)))

	  (let ((latest-pts* (if (not theatre-only?) 
				 (direct-exclude-cells 
				  formula 
				  latest-pts
				  (mapcar #'(lambda (i) (nth i *vars-table*)) lower-vars))
			       latest-pts)))
	    (when (not (= num-cells-before (length latest-pts*)))

	      (fmt 1.5 "~%  :: Direct cell exclusion reduced number of new cells from ~A to ~A.~%"
		   num-cells-before (length latest-pts*))
	      (setq num-cells-before (length latest-pts*)))

	    (when (> num-cells-before 0)
	      (fmt 2 "~% Running AP-CAD stage given as n-theatre(~A).~%" d))

	    (setq latest-pts (process-cells-by-stage 
			      latest-pts*
			      (mapcar #'(lambda (i) (nth i *vars-table*)) lower-vars)
			      formula
			      (funcall theatre d))))
	  (let ((num-cells-after (length latest-pts)))
	    (when (not (= num-cells-before num-cells-after))
	      (fmt 1.5 "~%  !! AP-CAD Cell exclusion reduced number of new cells from ~A to ~A.~%"
		   num-cells-before num-cells-after))
	      (when (= num-cells-after 0)
		(setq short-circuit? t)
		(fmt 1.5 "  :: Cell exclusion has reduced number of cells to 0, so we can short-circuit cad construction!~%~%")))))

      (setq lift-vars (cdr lift-vars)))
    (fmt 2 "~%  Final var-order: ~A." (mapcar #'(lambda (i) (nth i *vars-table*)) lower-vars))
    (fmt 1.5 "~%  Success!  Cell decomposition complete (~A sample pts).~%" (length latest-pts))
    (fmt 2.5 "  Printing ~A sample points from full-dimensional cells homeomorphic to (R^~A):~%~%    ~A.~%~%"
	 (length latest-pts) (length lower-vars) latest-pts)
    latest-pts))

;;;
;;; FD-CAD: Given a set of n-dimensional polynomials construct a CAD of
;;;  n-dimensional space using sample points only from full-dimensional
;;;  cells.
;;;
;;; Since we're only interested in satisfiability, we need only store
;;;  the highest dimensional set of sample points.
;;;
;;; Also, if :formula is given, then we will perform partial fdcad by
;;;  not lifting over cells which falsify any literals in the input
;;;  formula (recall we're dealing only with conjunctions).
;;;
;;; We return an array of n-dimensional sample points.
;;;

(defun fd-cad (ps var-order &key epsilon formula factor?)
  (fmt 3 "~% [cad: Computing projection factor set (pfs)]")
  (let ((projfs (fd-cad-project ps var-order :factor? factor?))
	(lift-vars (reverse var-order))
	(lower-vars) (latest-pts) (short-circuit?))
    (fmt 2 "~% [cad: Beginning full-dimensional lifting]")
    (loop for d from 0 to (1- (length lift-vars)) 
	  while (not short-circuit?) do
      (let ((cur-var (car lift-vars))
	    (cur-pfs (aref projfs d)))
	(cond ((= d 0)
	       (fmt 2 "~%   Computing base phase (R^1):")
	       (setq latest-pts
		     (mapcar #'list 
			     (coerce 
			      (ps-rational-sample-pts cur-pfs :epsilon epsilon)
			      'list)))
	       (fmt 2 "~%    ~A base rational sample points isolated: ~A.~%" 
		    (length latest-pts) latest-pts))
	      (t (fmt 2 "~%   Computing lifting from (R^~A) to (R^~A):~%" d (1+ d))
		 (fmt 2 "    Substituting ~A sample points in (R^~A) into (R^~A) pfs: ~%"
		      (length latest-pts) d (1+ d))
		 (fmt 4 "     pfs:  ~A,~%" (mapcar #'poly-alg-rep-to-prover-rep
						 cur-pfs))
		 (fmt 4 "     pts:  ~A,~%" latest-pts)
		 (fmt 4 "     lvs:  ~A.~%" (mapcar #'(lambda (i) 
						    (nth i *vars-table*)) 
						lower-vars))
		 (let ((new-pfs-instances
			(mapcar #'clean-rcs 
				(spts-subst-alg cur-pfs latest-pts lower-vars))))
		   (fmt 4 "     npfs: ~A.~%" 
			(mapcar #'(lambda (ps) 
				    (mapcar #'poly-alg-rep-to-prover-rep ps))
				new-pfs-instances))
		   (fmt 3 "~%    Isolating roots and sample points of induced univariate families: ~%")
		   (let ((new-latest-pts) (cur-instance 0))
		     (dolist (pfs-instance new-pfs-instances)
		       (let ((new-roots 
			      (coerce (ps-rational-sample-pts pfs-instance :epsilon epsilon) 'list))
			     (parent-sample-pt (nth cur-instance latest-pts)))
			 (fmt 4 "     upts: ~A.~%" new-roots)
			 (let ((hd-sample-pts
				(mapcar #'(lambda (r) (cons r parent-sample-pt)) new-roots)))
			   (fmt 4 "     nhds: ~A.~%" hd-sample-pts)
			   (setq new-latest-pts (append hd-sample-pts new-latest-pts))))
		       (setq cur-instance (1+ cur-instance)))
		     (setq latest-pts new-latest-pts)))))
	(setq lower-vars (cons cur-var lower-vars)))

      ;;
      ;; Direct partial CAD check: Remove the new sample points which lead to direct
      ;;  inconsistency, if formula (conjunctive case) is given.
      ;;

      (when (and formula (cdr lift-vars))
	(let ((num-cells-before (length latest-pts)))
	  (setq latest-pts (direct-exclude-cells 
			    formula 
			    latest-pts
			    (mapcar #'(lambda (i) (nth i *vars-table*)) lower-vars)))
	  (let ((num-cells-after (length latest-pts)))
	    (when (not (= num-cells-before num-cells-after))
	      (fmt 1.5 "~%  :: Direct cell exclusion reduced number of new cells from ~A to ~A.~%"
		   num-cells-before num-cells-after)
	      (when (= num-cells-after 0)
		(setq short-circuit? t)
		(fmt 1.5 "  :: Direct cell exclusion has reduced number of cells to 0, so we can short-circuit cad construction!~%~%"))))))

      (setq lift-vars (cdr lift-vars)))
    (fmt 2 "~%  Final var-order: ~A." (mapcar #'(lambda (i) (nth i *vars-table*)) lower-vars))
    (fmt 1.5 "~%  Success!  Cell decomposition complete (~A sample pts).~%" (length latest-pts))
    (fmt 2.5 "  Printing ~A sample points from full-dimensional cells homeomorphic to (R^~A):~%~%    ~A.~%~%"
	 (length latest-pts) (length lower-vars) latest-pts)
    latest-pts))

;;;
;;; EVAL-SPT-SUBST: Given a case in prover notation, an n-dimensional
;;;  sample point and a list of n variables, instantiate the case upon
;;;  the sample point and evaluate it, returning true or false.
;;;  This is only for full-dimensional sample points.
;;;

(defun eval-spt-subst (c vars pt)
  (dolist (v vars)
    (let ((cur-pt (car pt)))
      (setq c (subst cur-pt v c))
      (setq pt (cdr pt))))
  (fmt 4 "  Evaluating: ~A :: " `(and ,@c))
  (let ((result (eval `(and ,@c))))
    (fmt 4 "~A.~%" (if result "sat" "unsat"))
    result))

;;;
;;; VAR-IDS: Given a list of variable symbols, convert it into
;;;  a list of variable IDs w.r.t. *VARS-TABLE*.
;;;

(defun var-ids (vs)
  (mapcar #'(lambda (v)
	      (find-var v *vars-table* 0))
	  vs))

;;;
;;; FD-CAD-SAT?: Given an open RAHD case, check to see if it is
;;;  satisfied by computing a full-dimensional CAD.
;;;
;;; Case is given in prover notation.
;;;

;;;
;;; *** Must only allow *sat-model* to be adjusted if
;;;  gather-strict-ineqs is the entire case!
;;;

(defun fd-cad-sat? (c &key epsilon partial? factor? proj-order-greedy? var-order)
  (let* ((ps* (mapcar #'(lambda (l)
			  `(- ,(cadr l)
			      ,(caddr l)))
		      c))
	 (vs (if var-order
		 (mapcar (lambda (x)
			   (let ((id 0))
			     (dolist (v *vars-table*)
			       (if (eq v x) (return id)
				 (setq id (1+ id))))))
			 var-order)
	       (if proj-order-greedy? 
		   (var-ids (vs-proj-order-greedy 
			     (mapcar #'poly-prover-rep-to-alg-rep ps*)))
	       (vs-proj-order-brown ps*))))
	 (vs* (mapcar #'(lambda (i) (nth i *vars-table*)) vs))
	 (ps (mapcar #'poly-prover-rep-to-alg-rep ps*))
	 (spts (fd-cad ps vs
		       :epsilon epsilon
		       :formula (when partial? c)
		       :factor? factor?)))
    (fmt 2 "~% Extracted polynomials: ~A.~%" ps*)
    (fmt 2 "~% Sample points computed.~%")
    (fmt 2 "~% Beginning evaluation of formula.~%")
    (let ((sat? nil))
      (while (and (not sat?) (consp spts))
	(let ((spt (car spts)))
	  (setq sat? (when (eval-spt-subst
			    c
			    vs*
			    spt)
		       spt))
	  (setq spts (cdr spts))))
      (let ((model))
	(cond (sat?
	       (let ((sat-pt sat?))
		 (loop for i from 0 to (1- (length vs*)) do
		       (setq model (cons (list (car vs*) (car sat-pt)) model))
		       (setq vs* (cdr vs*))
		       (setq sat-pt (cdr sat-pt))))
	       (fmt 2 "~% Satisfiable!~%  Satisfying assignment: ~A.~%" model))
	      (t (fmt 2 "~% Unsatisfiable!~%")))
      (when sat? model)))))

;;;
;;; APCAD-FD-SAT?
;;;

(defun apcad-fd-sat? (c theatre &key epsilon partial? factor? proj-order-greedy? var-order theatre-only?)
  (let* ((ps* (mapcar #'(lambda (l)
			  `(- ,(cadr l)
			      ,(caddr l)))
		      c))
	 (vs (if var-order
		 (mapcar (lambda (x)
			   (let ((id 0))
			     (dolist (v *vars-table*)
			       (if (eq v x) (return id)
				 (setq id (1+ id))))))
			 var-order)
	       (if proj-order-greedy? 
		   (var-ids (vs-proj-order-greedy 
			     (mapcar #'poly-prover-rep-to-alg-rep ps*)))
	       (vs-proj-order-brown ps*))))
	 (vs* (if var-order var-order 
		(mapcar #'(lambda (i) (nth i *vars-table*)) vs)))
	 (ps (mapcar #'poly-prover-rep-to-alg-rep ps*))
	 (spts (apcad-fd ps vs theatre
		       :epsilon epsilon
		       :formula (when partial? c)
		       :factor? factor?
		       :theatre-only? theatre-only?)))
    (fmt 3 "~% Extracted polynomials: ~A.~%" ps*)
    (fmt 3 "~% Sample points computed.~%")
    (fmt 3 "~% Beginning evaluation of formula.~%")
    (let ((sat? nil))
      (while (and (not sat?) (consp spts))
	(let ((spt (car spts)))
	  (setq sat? (when (eval-spt-subst
			    c
			    vs*
			    spt)
		       spt))
	  (setq spts (cdr spts))))
      (let ((model))
	(cond (sat?
	       (let ((sat-pt sat?))
		 (loop for i from 0 to (1- (length vs*)) do
		       (setq model (cons (list (car vs*) (car sat-pt)) model))
		       (setq vs* (cdr vs*))
		       (setq sat-pt (cdr sat-pt))))
	       (fmt 3 "~% Satisfiable!~%  Satisfying assignment: ~A.~%" model))
	      (t (fmt 3 "~% Unsatisfiable!~%")))
      (when sat? model)))))

;;;
;;; APCAD-FD-ON-CASE: Apply APCAD-FD-SAT to a conjunctive case.
;;;    To do so, we first extract only the strict inequalities.
;;;   Note that unless c consists only of strict inequalities, then
;;;    we can't trust SAT answers, only UNSAT.
;;;

(defun apcad-fd-on-case (c theatre &key (factor? t) proj-order-greedy? var-order (partial? t) theatre-only?)
  (let ((sc (gather-strict-ineqs c)))
    (if sc 
	(let ((s? (apcad-fd-sat? 
		   sc 
		   theatre
		   :partial? partial?
		   :factor? factor?
		   :proj-order-greedy? proj-order-greedy?
		   :var-order var-order
		   :theatre-only? theatre-only?)))
	  (cond (s? (if (= (length sc) (length c))
			(let ((judgment 
                               `(:SAT (:MODEL 
                                       ,(union (get-active-vt-bindings)
                                               s?
                                               :test 'equal)))))
			  (setq *sat-model* judgment)
			  judgment)
		      c))
		(t `(:UNSAT 
		     (:NO-SATISFYING-VECTOR-IN-FULL-DIMENSIONAL-CELLS)))))
      c)))

;;;
;;; FDEP-CAD-ON-CASE: Apply FD-CAD-SAT to a conjunctive case.
;;;    To do so, we first extract only the strict inequalities.
;;;   Note that unless c consists only of strict inequalities, then
;;;    we can't trust SAT answers, only UNSAT.
;;;

(defun fdep-cad-on-case (c &key (factor? t) proj-order-greedy? var-order partial?)
  (let ((sc (gather-strict-ineqs c)))
    (if sc 
	(let ((s? (fd-cad-sat? 
		   sc 
		   :partial? partial?
		   :factor? factor?
		   :proj-order-greedy? proj-order-greedy?
		   :var-order var-order)))
	  (cond (s? (if (= (length sc) (length c))
			(let ((judgment 
                               `(:SAT (:MODEL 
                                       ,(union (get-active-vt-bindings)
                                               s?
                                               :test 'equal)))))
			  (setq *sat-model* judgment)
			  judgment)
		      c))
		(t `(:UNSAT 
		     (:NO-SATISFYING-VECTOR-IN-FULL-DIMENSIONAL-CELLS)))))
      c)))

;;;
;;; DEG-VARS-IN-P: Given a polynomial in algebraic notation and a variable,
;;;  return a hash-table of the form ( (key=var-id , val=max-pow) ) where
;;;  max-pow is the maximal power that var-id appears in the polynomial.
;;;

(defun deg-vars-in-p (p)
  (let ((out (make-hash-table)))
    (dolist (m p)
      (let ((pp (cdr m)))
	(dolist (vp pp)
	  (let ((var-id (car vp))
		(pow (cdr vp)))
	    (multiple-value-bind 
		(max-pow in-hash?) 
		(gethash var-id out)
	      (if in-hash?
		  (when (>= pow max-pow)
		    (setf (gethash var-id out) pow))
		(setf (gethash var-id out) pow)))))))
    out))

;;;
;;; MERGE-VIP-HASHES: Given two hash-tables of the form ( (key=var-id , val=max-pow) ),
;;;  merge them (taking the maximum of the two power entries for any given var-id if
;;;  it is present in both hash tables.)
;;;

(defun merge-vip-hashes (h0 h1)
  (let ((out (make-hash-table)))
    (loop for var-id being the hash-keys in h0 using (hash-value max-pow)
	  do (setf (gethash var-id out) max-pow))
    (loop for h1-var-id being the hash-keys in h1 using (hash-value h1-max-pow)
	  do 
	  (multiple-value-bind 
	      (out-max-pow in-out?) 
	      (gethash h1-var-id out)
	    (if in-out?
		(when (>= h1-max-pow out-max-pow)
		  (setf (gethash h1-var-id out) h1-max-pow))
	      (setf (gethash h1-var-id out) h1-max-pow))))
    out))
 
;;;
;;; VS-PROJ-ORDER-BROWN: Order variables using more-or-less a heuristic
;;;  communicated to us by Chris Brown.
;;;
;;; Polynomials are given in prover notation.
;;; List of variable-ids is returned.
;;;

(defun vs-proj-order-brown (ps)
  (let ((h))
    (dolist (p ps)
      (let ((p* (poly-prover-rep-to-alg-rep p)))
	(if (not h)
	    (setq h (deg-vars-in-p p*))
	  (setq h (merge-vip-hashes 
		   h
		   (deg-vars-in-p p*))))))
    (let ((vmp-lst))
	   (maphash #'(lambda (x y)
			(setq vmp-lst (cons (cons x y) vmp-lst)))
		    h)
	   (let ((sorted-vars-lst 
		  (sort vmp-lst #'(lambda (x y)
				    (< (cdr x) (cdr y))))))
	     (mapcar #'car sorted-vars-lst)))))

;;;
;;; VS-PROJ-ORDER: Given a set of polynomials, compute a projection
;;;  order from the variables given.  Right now, we use no heuristics
;;;  for this and just use more-or-less the order they appear.
;;;
;;; Polynomials are given in prover notation.
;;; Variable list returned is a list of variable IDs (indices in *VARS-TABLE*).
;;; We then project them away from left to right.
;;;

(defun vs-all (ps)
  (mapcar #'(lambda (v)
	      (let ((i (find-var v *vars-table* 0)))
		(if (not i)
		    (progn 
		      (setq *vars-table*
			    (append *vars-table* `(,v)))
		      (1- (length *vars-table*)))
		  i)))
	  (let ((vs))
	    (dolist (p ps)
	      (setq vs (union vs (gather-vars p))))
	    vs)))

;;;
;;; BM-PROJ-1: 1-step of Brown-McCallum projection.
;;;

(defun bm-proj-1 (ps var-id)
  (let ((lcs (lcoeffs ps var-id))
        (ds (discrs ps var-id))
        (rs (ress ps var-id)))
    (mapcar #'(lambda (p) 
                (poly-prover-rep-to-alg-rep
                 (poly-expand-expts p)))
            (sqr-free-dps
             (mapcar #'poly-alg-rep-to-prover-rep
                     (clean-rcs
                      (union (union lcs ds :test 'equal) 
                             rs
                             :test 'equal)))))))

;;;
;;; VS-PROJ-ORDER-GREEDY: Compute a projection order using the greedy
;;;  method of Seidl et al.
;;; 
;;; We accept the polynomials in algebraic notation.
;;; We return a list in algebraic notation (VAR-ID's).
;;;

(defun vs-proj-order-greedy (ps)
  (let* ((all-vs (vs-all (mapcar #'poly-alg-rep-to-prover-rep ps)))
         (num-vars (length all-vs))
         (remaining-vs all-vs)
         (out-order (make-array num-vars))
         (last-ps ps))
    (fmt 3 "~% Computing FD-CAD projection order greedily
  (using Brown-McCallum FD projection operator).~%")
    (loop for i from 0 to (1- num-vars) do
          (fmt 3 "~%  Determining variable ~A..." (1+ i))
          (cond ((= i (1- num-vars))
                 (fmt 3 "... Winner: ~A (final var, so trivial choice)."
                      (nth (car remaining-vs) *vars-table*))
                 (setf (aref out-order (1- num-vars)) (car remaining-vs)))
                (t (let ((winning-var) (winning-value))
                     (dolist (v remaining-vs)
                       (let ((candidate-value (ps-sum-mdeg (bm-proj-1 last-ps v))))
                         (cond ((not winning-var)
                                (setq winning-var v)
                                (setq winning-value candidate-value))
                               ((< candidate-value winning-value)
                                (setq winning-var v)
                                (setq winning-value candidate-value)))))
                     (setf (aref out-order i) winning-var)
                     (fmt 3 "... Winner: ~A.~%" (nth winning-var *vars-table*))
                     (setq remaining-vs 
                           (set-difference remaining-vs `(,winning-var)))))))
    (let ((proj-order-lst 
           (mapcar #'(lambda (x) (nth x *vars-table*))
                   (coerce out-order 'list))))
      (fmt 3 "~%~% Projection order: ~A.~%~%" proj-order-lst)
      proj-order-lst)))

;;;
;;; VS-PROJ-ORDER-GREEDY-ON-CASE: Given a case, compute a projection order
;;;  for it using the Seidl greedy approach.
;;;

(defun vs-proj-order-greedy-on-case (c)
  (let ((ps (mapcar 
             #'(lambda (x) 
                 (poly-prover-rep-to-alg-rep
                  `(- ,(cadr x) ,(caddr x))))
             c)))
    (vs-proj-order-greedy ps)))

;;;
;;; MAKE-CAD-TEST: Make a simple test instance for our fdcad.
;;;

(defparameter *ps* nil)
(defparameter *vs* nil)

(defun make-cad-test (ps)
  (let ((new-ps
	 (mapcar #'(lambda (p)
		     (poly-prover-rep-to-alg-rep
		      (poly-expand-expts
		       (term-to-bin-ops p))))
		 ps)))
    (setq *ps* new-ps)
    (setq *vs*
	  (mapcar #'(lambda (v)
		      (find-var v *vars-table* 0))
		  (let ((vs))
		    (dolist (p (mapcar #'poly-alg-rep-to-prover-rep new-ps))
		      (setq vs (union vs (gather-vars p))))
		    vs)))))

;;; 
;;; *** Standard CAD Projection Operator ***
;;;
;;; Given a set of polynomials P and a var id VAR-ID, compute a projection
;;;  factor set for P w.r.t. the variable whose index is VAR-ID.
;;;
;;; Polynomials are given in algebraic representation.
;;;

;; (defun std-cad-project (ps var-id)
;;   (let ((proj-factor-set nil)
;; 	(ps-p-hashes (make-hash-table :test 'equal)))
;;     (dolist (p ps)
;;       (let* ((p-hash (let ((known? (gethash p ps-p-hashes)))
;; 		       (if known? known? 
;; 			 (let ((p-hash* (p-hash-in-v p var-id)))
;; 			   (setf (gethash p ps-p-hashes) p-hash*)
;; 			   p-hash*))))
;; 	     (deg-p (p-hash-deg p-hash)))
;; 	(when (>= deg-p 2)
;; 	  (let ((trunc-p (trunc-p-hash p-hash var-id)))
;; 	    (dolist (r trunc-p)
;; 	      (let ((sres-seq-r-dr/dv (sres-seq-p-dp/dv r var-id)))
;; 		(setq proj-factor-set
;; 		      (union proj-factor-set sres-seq-r-dr/dv))))))))
;;     (let ((trunc-set-ps (trunc-set ps var-id)))
;;       (dolist ((
;;     proj-factor-set))

;; Some APCAD examples:

;; (apcad-fd-on-case '((> (* x x) (+ (* x w) y)) 
;; 		    (> y z) (> z w) (> (* w x) x) 
;; 		    (> x 0) (< x 1) 
;; 		    (> y 0) (< y 10))
;;        #'interval-theatre)

;; ; vs

;; (fdep-cad-on-case '((> (* x x) (+ (* x w) y)) 
;; 		    (> y z) (> z w) (> (* w x) x) 
;; 		    (> x 0) (< x 1) 
;; 		    (> y 0) (< y 10)))
