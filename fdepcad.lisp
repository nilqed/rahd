;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Full-dimensional abstract partial cylindrical algebraic decomposition.
;;;
;;; (Explained in my PhD dissertation).
;;;
;;;  Note: We support one projection operator -- 
;;;   (-) Brown-McCallum projection (which is valid for f.d. lifting).
;;;
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
;;;            last updated on  06-December-2010.
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
	     (fmt 3 "~%   Projection factor set found in PFS cache! ~%")
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
      
      (fmt 3 "~%   cad pfs component for dimension ~A:~%    ~A.~%"
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

	      (fmt 3 "~%   cad pfs component for (R^~A) (eliminated ~A):~%    ~A.~%"
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
    (fmt 3 "~% [cad: Beginning full-dimensional lifting]")
    (loop for d from 0 to (1- (length lift-vars)) 
	  while (not short-circuit?) do
      (let ((cur-var (car lift-vars))
	    (cur-pfs (aref projfs d)))
	(cond ((= d 0)
	       (fmt 3 "~%   Computing base phase (R^1):")
	       (setq latest-pts
		     (mapcar #'list 
			     (coerce 
			      (ps-rational-sample-pts cur-pfs :epsilon epsilon)
			      'list)))
	       (fmt 3 "~%    ~A base rational sample points isolated: ~A.~%" 
		    (length latest-pts) latest-pts))
	      (t (fmt 3 "~%   Computing lifting from (R^~A) to (R^~A):~%" d (1+ d))
		 (fmt 3 "    Substituting ~A sample points in (R^~A) into (R^~A) pfs: ~%"
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
	      (fmt 3 "~%  :: Direct cell exclusion reduced number of new cells from ~A to ~A.~%"
		   num-cells-before num-cells-after)
	      (when (= num-cells-after 0)
		(setq short-circuit? t)
		(fmt 3 "  :: Direct cell exclusion has reduced number of cells to 0, so we can short-circuit cad construction!~%~%"))))))

      (setq lift-vars (cdr lift-vars)))
    (fmt 3 "~%  Final var-order: ~A." (mapcar #'(lambda (i) (nth i *vars-table*)) lower-vars))
    (fmt 3 "~%  Success!  Cell decomposition complete (~A sample pts).~%" (length latest-pts))
    (fmt 4 "  Printing ~A sample points from full-dimensional cells homeomorphic to (R^~A):~%~%    ~A.~%~%"
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

(defun fd-cad-sat? (c &key epsilon partial? factor? proj-order-greedy?)
  (let* ((ps* (mapcar #'(lambda (l)
			  `(- ,(cadr l)
			      ,(caddr l)))
		      c))
	 (vs (if proj-order-greedy? 
		 (var-ids (vs-proj-order-greedy 
			   (mapcar #'poly-prover-rep-to-alg-rep ps*)))
	       (vs-all ps*)))
	 (vs* (mapcar #'(lambda (i) (nth i *vars-table*)) vs))
	 (ps (mapcar #'poly-prover-rep-to-alg-rep ps*))
	 (spts (fd-cad ps vs
		       :epsilon epsilon
		       :formula (when partial? c)
		       :factor? factor?)))
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
;;; FDEP-CAD-ON-CASE: Apply FD-CAD-SAT to a conjunctive case.
;;;    To do so, we first extract only the strict inequalities.
;;;   Note that unless c consists only of strict inequalities, then
;;;    we can't trust SAT answers, only UNSAT.
;;;

(defun fdep-cad-on-case (c &key (factor? t) proj-order-greedy?)
  (let ((sc (gather-strict-ineqs c)))
    (if sc 
	(let ((s? (fd-cad-sat? 
		   sc 
		   :partial? t
		   :factor? factor?
		   :proj-order-greedy? proj-order-greedy?)))
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
;;; VS-PROJ-ORDER: Given a set of polynomials, compute a projection
;;;  order from the variables given.  Right now, we use no heuristics
;;;  for this and just use more-or-less the order they appear.
;;;
;;; Polynomials are given in prover notation.
;;; Variable list returned is a list of variable IDs (indices in *VARS-TABLE*).
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