;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Proof strategy processing and execution.
;;;
;;; Written by Grant Olney Passmore
;;; Postdoc, Cambridge-Edinburgh EPSRC grant
;;;   ``Automatic Proof Procedures for Polynomials and Special Functions.''
;;; Postdoctoral Associate, Clare Hall, University of Cambridge
;;; Research Associate, LFCS, University of Edinburgh
;;;
;;; The following institutions have provided support for RAHD development
;;;  through funding the following positions for me (Passmore):
;;;    - Ph.D. Student, University of Edinburgh,
;;;    - Visiting Fellow, SRI International,
;;;    - Research Intern, Microsoft Research,
;;;    - Visiting Researcher, INRIA/IRISA.
;;;
;;; These positions have been crucial to RAHD progress and we thank the host 
;;;  institutions and groups very much for their support and encouragement.
;;;
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/.
;;; 
;;; This file: began on         13-December-2010,
;;;            last updated on  14-March-2011.
;;;

;;;
;;; *PROOF-STRATEGIES*: A global hash-table for defined proof strategies.
;;;   (key is symbol naming proof strategy, value is strategy S-expression).
;;;

(defparameter *proof-strategies*
  (make-hash-table :test 'equal))

;;;
;;; Return a list of all declared proof strategies.
;;; (list is a list of symbols).
;;;

(defun all-strats ()
  (let ((out))
    (maphash #'(lambda (x y)
                 (declare (ignore y))
                 (setq out (cons x out)))
             *proof-strategies*)
  out))

;;;
;;; Print all available defined strategies.
;;;

(defun print-all-strats (&key id-nums)
  (fmt 0 "Defined proof strategies:~%~%")
  (if id-nums
      (let ((id 0))
        (dolist (s (all-strats))
          (fmt 0 " ~A. ~A~%" id s)
          (setq id (1+ id))))
    (fmt 0 "~{ ~A~%~}" (all-strats))))

;;;
;;; Get strategy by numerical ID.
;;;

(defun get-strat-by-num (id)
  (let ((strats (all-strats)))
    (nth (if (and (<= 0 id) (<= id (1- (length strats))))
             id
           0)
         strats)))
;;;
;;; Insert a strategy (symbol name, string-rep, S-expression body) triple
;;;  into the *proof-strategies* hash table, keyed by symbol name.
;;;

(defun add-strat (name strat-str body)
  (setf (gethash name *proof-strategies*) (cons strat-str body)))

;;;
;;; Parse and then add a strategy to the repository.
;;; This is called `defining a strategy.'
;;;

(defun defstrat (name strat-str)
  (let ((parsed (p-strategy strat-str)))
    (add-strat name strat-str parsed)
    (fmt 1 "~% Parsed: ~A.~%
 Proof strategy ~A defined.~%" parsed name)))

;;;
;;; Given a strategy name (symbol), return the S-expression of the strategy.
;;;

(defun get-strat (name)
  (cdr (gethash name *proof-strategies*)))

;;;
;;; Print info about a particular strategy.
;;;

(defun print-strat (name-str)
  (let ((strat-name (intern (string-upcase name-str))))
    (let ((strat (get-strat strat-name)))
      (cond (strat 
	     (fmt 0 "--
Strategy Definition Record
--
 Name: ~A,
 Defn: ~A.~%~%" name-str strat))
	    (t (fmt 0 "Error: No strategy named ~A defined.~%~%"
		    name-str))))))


;;;
;;; Match CMF string to CMF function.  Note that we return the
;;;  ***unmapped*** version of the CMF, i.e., only the point-wise
;;;  CMF that operates on a single case.  The strategy execution
;;;  machinery will handle mapping such a CMF over the cases in
;;;  question.
;;;
;;; We now also include possible parameter/argument names for each
;;;  cmf as the final (third) entry in each row.  These should appear
;;;  as the name they should be interned in the :keyword package.
;;;

(defparameter *cmf-str-fcn-table*
  `(("simp-arith"       ,#'arith-simplify-case       nil)
    ("apcad-fd"         ,#'fdep-cad-on-case          (PROJ-ORDER-GREEDY? FACTOR? STAGE THEATRE))
    ("contra-eqs"       ,#'simply-incons*            nil)
    ("demod-num"        ,#'demodulate-numerically    nil)
    ("simp-gls"         ,#'simplify-ground-lits+rtv  nil)
    ("fert-tsos"        ,#'fertilize-trivial-squares nil)
    ("univ-sturm-ineqs" ,#'open-interval-univ-ineq   nil)
    ("canon-tms"        ,#'canonize-terms            nil)
    ("simp-zrhs"        ,#'zero-rhs                  nil)
    ("triv-ideals"      ,#'trivial-ideal             nil)
    ("rcr-ineqs"        ,#'ineqs-over-quotient-ring  nil)
    ("simp-real-null"   ,#'simp-real-nullstellensatz nil)
    ("rcr-svars"        ,#'fsvoqr                    nil)
    ("int-dom-zpb"      ,#'integral-domain-zpb       nil)
    ("int-dom-zpb-gen"  ,#'integral-domain-zpb-gen   nil)
    ("demod-lin"        ,#'derive-partial-demod-lins nil)
    ("interval-split"   ,#'split-term-for-case       (TERM))
    ("interval-cp"      ,#'icp-on-case               (MAX-CONTRACTIONS))
    ("satur-lin"        ,#'saturate-case-with-linear-orientations nil)
    ("full-gbrni"       ,#'full-gb-real-null-on-case nil)
    ("bounded-gbrni"    ,#'bgbrnull-case-wrapper     (GB-BOUND ICP-PERIOD UNION-CASE SUMMAND-LEVEL SATURATE-BY))
    ("quick-sat"        ,#'qsi-on-case               (GEN-PT-BOUND))
    ("factor-sign"      ,#'factor-sign-case          nil)
    ("ruleset"          ,#'apply-ruleset-to-case     (NAME))
    ("apcad-fd"         ,#'fdep-cad-on-case          (PROJ-ORDER-GREEDY? FACTOR? STAGE THEATRE))
    ("split-ineqs"      ,#'split-ineqs-cmf           nil)
    ))

(defun install-cmf (&key cmf-str cmf-fcn cmf-args)
  (let ((new-table (remove-if (lambda (x) (equal (car x) cmf-str))
			      *cmf-str-fcn-table*)))
  (setq *cmf-str-fcn-table*
	(append new-table
		(list (list cmf-str cmf-fcn cmf-args))))))
    
(defun cmf-from-str (str)
  (cadr (assoc str *cmf-str-fcn-table* :test 'equal)))

(defun avail-cmfs ()
  (let ((cmfs-lst (mapcar #'(lambda (x) (car x)) *cmf-str-fcn-table*)))
    (sort cmfs-lst #'string<)))

(defun cmf-args-all ()
  (let ((out nil))
    (mapcar #'(lambda (x)
                (let ((args (caddr x)))
                  (setq out (union out args :test 'equal))))
            *cmf-str-fcn-table*)
    (sort out #'string<)))

;;;
;;; CMF symbol to function hash-table and look-up.
;;; * This is used for fast CMF look-up during proof strategy execution.
;;;
;;; The entries of the hash-table are pairs of the form:
;;;   (CMF-FCN . CMF-ARGS-LST).
;;;

(defparameter *cmf-sym-hash* 
  (make-hash-table :test 'eq))

(defun build-cmf-sym-hash ()
  (dolist (cmf-str-rec *cmf-str-fcn-table*)
    (let ((cmf-sym (intern (string-upcase (car cmf-str-rec))))
          (cmf-fcn (cadr cmf-str-rec))
          (cmf-args (caddr cmf-str-rec)))
      (setf (gethash cmf-sym *cmf-sym-hash*) 
            (cons cmf-fcn cmf-args)))))

(defun avail-cmfs-sym ()
  (let ((out))
    (maphash #'(lambda (x y)
                 (declare (ignore y))
                 (setq out (cons x out)))
             *cmf-sym-hash*)
    out))

(defun cmf-from-sym (s)
  (car (gethash s *cmf-sym-hash*)))

(defun cmf-args-from-sym (s)
  (cdr (gethash s *cmf-sym-hash*)))

(build-cmf-sym-hash)

;;;
;;; EVAL-COND: Evaluate a proof strategy condition w.r.t. the given
;;;  primitive case measures.  This condition has already been parsed 
;;;  into an S-expression.
;;;

(defun eval-strategy-cond (sc dim deg nl bw)
  (cond ((not (consp sc))
         (cond ((eq sc 'DIM) dim)
               ((eq sc 'DEG) deg)
               ((eq sc 'NL) nl)
               ((eq sc 'BW) bw)
               ((numberp sc) sc)
               (t (break "Unexpected value in strategy conditional."))))
        ((and (equal (length sc) 2)
              (eq (car sc) '~))
         (not (eval-strategy-cond (cadr sc) dim deg nl bw)))
        (t (let ((op (car sc))
                 (x (cadr sc))
                 (y (caddr sc)))
             (case op
               (+ (+ (eval-strategy-cond x dim deg nl bw)
                     (eval-strategy-cond y dim deg nl bw)))
               (- (- (eval-strategy-cond x dim deg nl bw)
                     (eval-strategy-cond y dim deg nl bw)))
               (* (* (eval-strategy-cond x dim deg nl bw)
                     (eval-strategy-cond y dim deg nl bw)))
               (expt (expt (eval-strategy-cond x dim deg nl bw)
                           (eval-strategy-cond y dim deg nl bw)))
               (> (> (eval-strategy-cond x dim deg nl bw)
                     (eval-strategy-cond y dim deg nl bw)))
               (>= (>= (eval-strategy-cond x dim deg nl bw)
                       (eval-strategy-cond y dim deg nl bw)))
               (= (= (eval-strategy-cond x dim deg nl bw)
                     (eval-strategy-cond y dim deg nl bw)))
               (<= (<= (eval-strategy-cond x dim deg nl bw)
                       (eval-strategy-cond y dim deg nl bw)))
               (< (< (eval-strategy-cond x dim deg nl bw)
                     (eval-strategy-cond y dim deg nl bw)))
               ((!= /=) (not (= (eval-strategy-cond x dim deg nl bw)
                                (eval-strategy-cond y dim deg nl bw))))
               (/\\ (and (eval-strategy-cond x dim deg nl bw)
                         (eval-strategy-cond y dim deg nl bw)))
               (\\/ (or (eval-strategy-cond x dim deg nl bw)
                        (eval-strategy-cond y dim deg nl bw)))
               (==> (or (not (eval-strategy-cond x dim deg nl bw))
                        (eval-strategy-cond y dim deg nl bw)))
               (otherwise (break "Unexpected operation in strategy conditional.")))))))

;;;
;;; CASE-DEG: Given a case, return its multivariate total degree.
;;;

(defun case-deg (c)
  (let ((max-deg 0))
    (dolist (a c)
      (let ((deg0 (poly-deg (poly-prover-rep-to-alg-rep (cadr a))))
            (deg1 (poly-deg (poly-prover-rep-to-alg-rep (caddr a)))))
        (setq max-deg (max max-deg deg0 deg1))))
    max-deg))

;;;
;;; CASE-DIM: Given a case, return its dimension.
;;;

(defun case-dim (c)
  (length (all-vars-in-conj c)))

;;;
;;; CASE-NL: Given a case, return its number of literals.
;;;

(defun case-nl (c)
  (length c))

;;;
;;; CASE-BW: Given a case, return its total coefficient bit-width.
;;;  *** This returns a float.
;;;

(defun case-bw (c)
  (let ((total-bw 0))
    (dolist (a c)
      (let ((bw0 (poly-bw (poly-prover-rep-to-alg-rep (cadr a))))
            (bw1 (poly-bw (poly-prover-rep-to-alg-rep (caddr a)))))
        (setq total-bw (+ total-bw bw0 bw1))))
    total-bw))

;;;
;;; APPLY-CMF-TO-CASE: Given a CMF symbol name and a case, 
;;;  apply the referenced CMF to the case.
;;;
;;; Note: We must do a linear pass to make sure that if
;;;  we are calling any CMF other than SIMP-TVS and the
;;;  case contains truth values T or NIL, then we must
;;;  apply SIMP-TVS first.
;;;

(defun apply-cmf-to-case (cmf-name c &key params)
  (let ((poly-case
         (remove-if #'(lambda (x) (eq x t)) c)))
    (cond ((member nil poly-case)
           '(:UNSAT :CONTAINS-NIL))
          (t
           (let ((cmf-fcn (cmf-from-sym cmf-name)))
             (if params 
                 (apply cmf-fcn (append (list poly-case) params))
               (funcall cmf-fcn poly-case)))))))

;;;
;;; UPDATE-CASE: Given a case ID, a case, a status, and an inference
;;;  step (e.g., a CMF name or a final judgment criteria), update
;;;  *gs* appropriately.
;;;

(defun update-case (i &key status case step)
  (let ((cur-status (aref *gs* i 2)))
    (when case (setf (aref *gs* i 1) case))
    (when status 
      (setf (aref *gs* i 2)
            `(,status ,@(append (list step)
                                (cdr cur-status)))))))

;;;
;;; CREATE-SUBGOAL: Given a (sub)goalkey and either a list of cases or
;;;  a formula in RAHD CNF form with :OR signifier, install the relevant 
;;;  formula as a new (sub)goal.
;;;
;;; Note: We then swap into this new subgoal as the active context.
;;; Note: The ':DISJ hasn't been removed from d-cnf before it is passed.
;;;

(defun create-subgoal (&key key cases d-cnf)
  (cond (cases
	 (g cases :goal-key key :overwrite-ok t))
	(d-cnf
	 (g (waterfall-disj-to-cnf (cdr d-cnf))
	    :goal-key key 
	    :overwrite-ok t))))

;;;
;;; ALL-CASES-REFUTED: Have all of the cases in the current goalset been
;;;  refuted?
;;;

(defun all-cases-refuted ()
  (let ((out t))
    (loop for i from 0 to (1- *gs-size*) do
	  (let ((c-status (car (aref *gs* i 2))))
	    (setq out (and (eq c-status ':UNSAT) out))))
    out))

;;;
;;; PROCESS-SUBGOAL: Given a current case ID, a formula which is the result
;;;  of a CMF upon the corresponding case, and a strategy to be used for
;;;  subgoal execution, we do the following:
;;;   1. Create a subgoal for the case ID with formula drawn from result
;;;       (the way this is done depends on if :CASES or :DISJ is used
;;;        as the subgoal signifier),
;;;   2. Run subgoal-strat on this new subgoal, if subgoal-strat is non-nil.
;;;   3. If subgoal-strat exists and succeeds in refuting the subgoal or 
;;;        finding a counter-expample, then we mark the corresponding case 
;;;        appropriately.
;;;   4. We then swap back to the case which generated the subgoal.
;;; 

(defun process-subgoal (i &key step result subgoal-strat)
  (let* ((parent-key *current-goal-key*)
	 (new-key (list parent-key i))
	 (vars-table *vars-table*))
    (case (car result)
      (:CASES (create-subgoal :key new-key :cases result))
      (:DISJ (create-subgoal :key new-key :d-cnf result)))
    (build-gs :do-not-split-ineqs? t)
    (when subgoal-strat
      (run-strategy subgoal-strat :subgoal-strat subgoal-strat))
    (let ((subgoal-decision
	   (cond ((all-cases-refuted) ':UNSAT)
		 (*sat-case-found?* ':SAT)
		 (t `(:UNKNOWN-WITH-SPAWNED-SUBGOAL ,new-key)))))
      (swap-to-goal parent-key)
      (update-case i
		   :status subgoal-decision
		   :step `(subgoal-spawned-from ,step then ,subgoal-strat))
      (when (or (eq subgoal-decision ':UNSAT)
                (eq subgoal-decision ':SAT))
	(setq *gs-unknown-size* (1- *gs-unknown-size*))))
    (setq *vars-table* vars-table)
    t))

;;;
;;; RUN-STRATEGY: A proof strategy interpreter (mapped over open cases).
;;;
;;; This function accepts a (parsed) S-expression presentation of a proof
;;;  strategy and then executes it upon the open cases.
;;;
;;; This function returns T iff the execution of strat resulted in a change
;;;  of at least one case in the current goalset.  Else, returns NIL.
;;;
;;; Note the keyword argument subgoal-strat.  When this argument is
;;;  given, its value (a strategy) will be executed upon any generated
;;;  subgoals.  When subgoal-strat is the same as strat, this then
;;;  gives a `recursive waterfall' execution of the strategy.
;;;

(defun run-strategy (strat &key from to case guard subgoal-strat)
  (cond 
   ((not (consp strat)) nil)
   ((eq (car strat) 'APPLY)
    (let* ((case-lb* (if case case (if from from 0)))
           (case-ub* (if case case (if to to (1- *gs-size*))))
           (case-lb (max case-lb* 0))
           (case-ub (min case-ub* (1- *gs-size*)))
           (progress?))
      (loop for i from case-lb to case-ub while (not *sat-case-found?*) do
            (setq *current-tactic-case* i)
	    (setq progress? nil)
            (let ((c (aref *gs* i 1))
                  (c-status (aref *gs* i 2)))
              (when (eq (car c-status) ':UNKNOWN)
                (cond 
                 ((eq c nil)
                  (update-case i 
                               :case c 
                               :status ':SAT 
                               :step ':EMPTY-CONJ))
                 ((member nil c)
                  (update-case i :case c 
                               :status ':UNSAT 
                               :step ':CONTAINS-NIL))
                 (t 
                  (let ((dim (case-dim c))
                        (deg (case-deg c))
                        (nl (case-nl c))
                        (bw (case-bw c)))
                    (let ((cmf-name (cadr strat))
                          (pass-guard? 
                           (if guard (eval-strategy-cond 
                                      guard
                                      dim deg nl bw)
                             t)))
                      (cond (pass-guard?
                             (fmt 1.5 "Executing cmf ~A on case ~A..." cmf-name i)
			     (finish-output)
                             (let ((result (apply-cmf-to-case cmf-name c :params (cddr strat))))
                               (cond 
                                ((not (equal c result))
                                 (setq progress? t)
                                 (if (eq result nil)
                                     (update-case i :case c 
                                                  :status ':SAT 
                                                  :step ':EMPTY-CONJ)
                                   (case (car result)
                                     (:UNSAT (update-case i 
                                                          :status ':UNSAT
                                                          :step
                                                          cmf-name)
                                             (setq *gs-unknown-size*
                                                   (1- *gs-unknown-size*)))
                                     (:SAT (update-case i 
                                                        :status ':SAT
                                                        :step
                                                        cmf-name)
                                           (setq *gs-unknown-size*
                                                 (1- *gs-unknown-size*))
                                           (when (and (not *sat-model*)
						      (aref *gs* i 3))
                                             (let* ((var-bindings (aref *gs* i 3))
                                                    (candidate-model 
                                                     `(:SAT (:MODEL ,var-bindings))))
                                               (setq *sat-model* candidate-model)))
                                           (setq *sat-case-found?* (list *current-goal-key* i)))
				     ((:CASES :DISJ)
				      (process-subgoal i 
						       :step cmf-name 
						       :subgoal-strat subgoal-strat
						       :result result))
                                     (otherwise
                                      (update-case i
                                                   :status ':UNKNOWN
                                                   :case result
                                                   :step cmf-name))))))
                               (fmt 1.5 "...Done(progress?=~A).~%" progress?)))
                            (t (fmt 1.5 "Case ~A did not pass guard ~A.~%" i
                                    guard))))))))))
      progress?))
   ((eq (car strat) 'THEN)
    (let* ((progress-0? (run-strategy (cadr strat) :subgoal-strat subgoal-strat))
           (progress-1? (run-strategy (caddr strat) :subgoal-strat subgoal-strat)))
      (or progress-0? progress-1?)))
   ((eq (car strat) 'IF)
    (let* ((guard+ (cadr strat))
           (strat0 (caddr strat))
           (strat1 (cadddr strat))
           (progress-0? 
            (run-strategy strat0
                          :guard (if guard `(/\\ ,guard+
                                                 ,@guard)
                                   guard+)
			  :subgoal-strat subgoal-strat))
           (progress-1?
            (run-strategy strat1
                          :guard (if guard `(/\\ (~ ,guard+)
                                                 ,@guard)
                                   `(~ ,guard+))
			  :subgoal-strat subgoal-strat)))
      (or progress-0? progress-1?)))
   ((eq (car strat) 'WHEN)
    (let ((guard+ (cadr strat))
	  (strat0 (caddr strat)))
      (run-strategy strat0
		    :guard (if guard `(/\\ ,guard+
					   ,@guard)
			     guard+)
		    :subgoal-strat subgoal-strat)))
   ((eq (car strat) 'RUN)
    (run-strategy (get-strat (cadr strat))
		  :subgoal-strat subgoal-strat))
   ((eq (car strat) 'REPEAT)
    (let ((strat-to-rep (cadr strat))
          (progress?)
          (single-step-progress? t))
      (loop while single-step-progress? do
            (setq single-step-progress?
                  (run-strategy strat-to-rep
				:subgoal-strat subgoal-strat))
            (when (and (not progress?)
                       single-step-progress?)
              (setq progress? t)))
      progress?))
   (t (error "Strategy command ~A not understood." strat))))

;;;
;;; Some auxiliary strategy parsing functions.
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)(in-package rahd)

(defun i2p-strat (a b c)
  (list b a c))

(defun proc-neg (a b)
  (declare (ignore a))
  `(not ,b))

(defun proc-if (a b c d)
  (declare (ignore a))
  `(if ,b ,c ,d))

(defun proc-when (a b c)
  (declare (ignore a))
  `(when ,b ,c))

(defun proc-try (a b c d)
  (declare (ignore a))
  `(try ,b ,c ,d))

(defun proc-then (a b c)
  (declare (ignore b))
  `(then ,a ,c))

(defun proc-apply (a b)
  (declare (ignore a))
  `(apply ,b))

(defun proc-apply-avl (a b c avl d)
  (declare (ignore a c d))
  (append `(apply ,b) avl))

(defun proc-apply-i (a)
  `(apply ,a))

(defun proc-apply-i-avl (a b avl d)
  (declare (ignore b d))
  (append `(apply ,a) avl))

(defun proc-run (a b)
  (declare (ignore a))
  `(run ,b))

(defun proc-run-avl (a b c avl d)
  (declare (ignore a c d))
  (append `(run ,b) avl))

(defun proc-true (a)
  (declare (ignore a))
  't)

(defun proc-false (a)
  (declare (ignore a))
  'nil)
  
(defun proc-cs-av (a b c)
  (declare (ignore b))
  `(,(intern (symbol-name a) 'keyword)
    ,c))

(defun proc-cs-avl (a b c)
  (declare (ignore b))
  (append a c))

(defun proc-print-trace (a b) ; print trace at verbosity b
  (declare (ignore a))
  `(print-trace ,b))
)

;;;
;;; Strategy grammar.
;;;

(yacc:define-parser strategy-parser
  (:start-symbol strategy)
  (:terminals 
   (dim deg nl bw rational int cmf cs-arg
        if when try by then apply run repeat
        strategy-name print-trace true false
        + - * = ==> |/\\| |\\/| |~| |;|
        |(| |)| > >= = /= != <= < |:=| |,| / ^ |[| |]|))
  (:precedence 
   ((:left then) (:left if) (:left run) 
    (:left ~) (:left |/\\|) (:left |\\/|) 
    (:left ^) (:left = /= > >= < <= |:=| |,|)
    (:left * /) (:left + -) (:left ==>)))

  (strategy
   action
   (if cond strategy strategy #'proc-if)
   (when cond strategy #'proc-when)
   (try strategy strategy by cond #'proc-try)
   (strategy |;| strategy #'proc-then)
   (repeat strategy #'list)
   (|[| strategy |]| #'k-2-3)
   (|(| strategy |)| #'k-2-3))

  (action
   (cmf #'proc-apply-i)
   (cmf |(| cs-avl |)| #'proc-apply-i-avl)
   (run strategy-name #'proc-run)
   (run strategy-name |(| cs-avl |)| #'proc-run-avl)
   (print-trace int #'proc-print-trace))
  
  (cs-avl
   cs-av
   (cs-av |,| cs-avl #'proc-cs-avl))

  (cs-av
   (cs-arg |:=| value #'proc-cs-av)
   (cs-arg |:=| strategy-name)
   (cs-arg |:=| theatre-name))

  (cond
   a-cond
   (cond |/\\| cond #'i2p-strat)
   (cond |\\/| cond #'i2p-strat)
   (cond ==> cond #'i2p-strat)
   (~ cond #'proc-neg)
   (|(| cond |)| #'k-2-3))

  (a-cond
   (value = value #'i2p)
   (value /= value #'i2p-neq)
   (value != value #'i2p-neq)
   (value > value #'i2p)
   (value >= value #'i2p)
   (value < value #'i2p)
   (value <= value #'i2p)
   (true #'proc-true)
   (false #'proc-false))

  (value
   measure                                  ; implicit action #'identity
   rational
   int
   (value + value #'i2p)
   (value - value #'i2p)
   (value * value #'i2p)
   (value ^ int #'i2p)
   (|(| value |)| #'k-2-3))

  (measure
   dim
   deg
   nl
   bw)

)

;;;
;;; Begin strategy lexing machinery.
;;;

;;;
;;; Recognise a CMF name string.  With the introduction of the
;;;  use-lst parameter, this function is now more generic -- it
;;;  is also used to try and find CMF arguments (see p-cmf-arg).
;;;

(defun p-cmf (s &key use-lst)
  (let ((sorted-cmfs-lst 
         (sort (if use-lst use-lst (avail-cmfs))
               #'(lambda (x y) (>= (length x) (length y))))))
    (if (equal s "") '(nil . "")
      (let ((cmf-found? nil) (cmf-str) (s-rst))
        (loop for c in sorted-cmfs-lst until cmf-found? do
              (let ((cmf-match? (p-match-prefix c s)))
                (when cmf-match?
                  (setq cmf-found? t)
                  (setq cmf-str c)
                  (setq s-rst cmf-match?))))
        (if cmf-found?
            (cons (string-upcase cmf-str) s-rst)
          (cons nil s))))))

;;;
;;; Is a string a valid CMF argument?  Note that this is in the
;;;  of our context-free strategy parsing, and so we only check
;;;  to see if the string is in fact the argument of *any* CMF.
;;;  We will do post processing to see if the arguments match up
;;;  to the right CMF once we have the strategy as an S-expression.
;;;

(defun p-cmf-arg (s)
  (p-cmf s :use-lst 
         (mapcar #'symbol-name (cmf-args-all))))

;;;
;;; Recognise a strategy name string.  This is done w.r.t. the 
;;;  context of the `currently defined' strategies.
;;;

(defun p-strat-name (s)
  (p-cmf s :use-lst
         (mapcar #'symbol-name (all-strats))))

;;;
;;; Convert a RAHD strategy string into a list of symbols.  These
;;;  will then be used to generate the lexer thunk.
;;;
;;; We return a list '(err? . result) where err? is t iff
;;;  there was an unexpected symbol.
;;;

(defun strategy-str-to-lex-syms (s) 
  (let ((out) (lex-err))
    (while (and (not (equal s "")) (not lex-err))
      (let* ((cmf? (p-cmf s))
             (cmf-arg? (when (not (car cmf?)) (p-cmf-arg s)))
             (strat? (when (not (or (car cmf?) (car cmf-arg?))) 
                       (p-strat-name s))))

        ;; Have we found a CMF/strategy name/arg?  If so, chunk it.

        (cond ((car cmf?)
               (setq out (cons (car cmf?) out))
               (setq s (cdr cmf?)))
              ((car cmf-arg?)
               (setq out (cons (car cmf-arg?) out))
               (setq s (cdr cmf-arg?)))
              ((car strat?)
               (setq out (cons (car strat?) out))
               (setq s (cdr strat?)))
              (t 
          
            ;; We haven't found a CMF/arg/strat name, so let's see what 
            ;;  we've really got.

               (let ((c (char s 0)) (l-s (length s)))
                 (let ((peek-1-c (when (> l-s 1) (char s 1)))
                       (peek-2-c (when (> l-s 2) (char s 2)))
                       (peek-3-c (when (> l-s 3) (char s 3)))
                       (peek-4-c (when (> l-s 4) (char s 4)))
                       (peek-5-c (when (> l-s 5) (char s 5))))
                   (cond ((and (equal l-s 1) 
                               (member c '(#\+ #\- #\* #\( #\) #\[ #\] #\= #\>
                                           #\< #\^ #\~ #\, #\;)))
                          (chunk-char c))
                         ((member c '(#\+ #\* #\( #\) #\[ #\] #\^ #\~ #\, #\;))
                          (chunk-char c))
                         ((and (equal c #\-) 
                               (not (member peek-1-c 
                                            '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))))
                          (chunk-char c))
                         ((or (equal c '#\Space) (equal c '#\Newline))
                          (setq s (subseq s 1 l-s)))
                         ((equal c #\=)
                          (cond ((and (equal peek-1-c '#\=)
                                      (equal peek-2-c '#\>))
                                 (chunk-prefix "==>"))
                                (t (chunk-char c))))
                         ((equal c '#\>)
                          (cond ((equal peek-1-c '#\=)
                                 (chunk-prefix ">="))
                                (t (chunk-char c))))
                         ((equal c '#\<)
                          (cond ((equal peek-1-c '#\=)
                                 (chunk-prefix "<="))
                                (t (chunk-char c))))
                         ((equal c '#\!)
                          (cond ((equal peek-1-c '#\=)
                                 (chunk-prefix "!="))
                                (t (chunk-char c))))
                         ((equal c '#\/)
                          (cond ((equal peek-1-c '#\=)
                                 (chunk-prefix "/="))
                                ((equal peek-1-c '#\\)
                                 (chunk-prefix "/\\"))
                                (t (chunk-char c))))
                         ((equal c '#\\)
                          (cond ((equal peek-1-c '#\/)
                                 (chunk-prefix "\\/"))
                                (t (chunk-char c))))
                         ((equal c '#\:)
                          (cond ((equal peek-1-c '#\=)
                                 (chunk-prefix ":="))
                                (t (chunk-char c))))
                         ((equal c '#\i)
                          (cond ((equal peek-1-c '#\f)
                                 (chunk-prefix "IF"))
                                (t (chunk-char c))))
                         ((equal c '#\t)
                          (cond ((and (equal peek-1-c '#\h)
                                      (equal peek-2-c '#\e)
                                      (equal peek-3-c '#\n))
                                 (chunk-prefix "THEN"))
                                (t (chunk-char c))))
                         ((equal c '#\r)
                          (cond ((and (equal peek-1-c '#\u)
                                      (equal peek-2-c '#\n))
                                 (chunk-prefix "RUN"))
                                ((and (equal peek-1-c '#\e)
                                      (equal peek-2-c '#\p)
                                      (equal peek-3-c '#\e)
                                      (equal peek-4-c '#\a)
                                      (equal peek-5-c '#\t))
                                 (chunk-prefix "REPEAT"))
                                (t (chunk-char c))))
                         ((equal c '#\a)
                          (cond ((and (equal peek-1-c '#\p)
                                      (equal peek-2-c '#\p)
                                      (equal peek-3-c '#\l)
                                      (equal peek-4-c '#\y))
                                 (chunk-prefix "APPLY"))
                                (t (chunk-char c))))
                         ((equal c '#\d)
                          (cond ((and (equal peek-1-c '#\i)
                                      (equal peek-2-c '#\m))
                                 (chunk-prefix "DIM"))
                                ((and (equal peek-1-c '#\e)
                                      (equal peek-2-c '#\g))
                                 (chunk-prefix "DEG"))
                                (t (chunk-char c))))
                         ((equal c '#\n)
                          (cond ((equal peek-1-c '#\l)
                                 (chunk-prefix "NL"))
                                (t (chunk-char c))))
			 ((equal c '#\w)
			  (cond ((and (equal peek-1-c '#\h)
				      (equal peek-2-c '#\e)
				      (equal peek-3-c '#\n))
				 (chunk-prefix "WHEN"))
				(t (chunk-char c))))
                         ((equal c '#\b)
                          (cond ((equal peek-1-c '#\y)
                                 (chunk-prefix "BY"))
                                ((equal peek-1-c '#\w)
                                 (chunk-prefix "BW"))
                                (t (chunk-char c))))
                         (t (let ((rat? (p-rational s)))
                              (if (car rat?)
                                  (progn 
                                    (setq out (cons (car rat?) out))
                                    (setq s (cdr rat?)))
                                (lex-error "Unexpected symbol" 
                                           :value c)))))))))))
    (mapcar #'(lambda (x)
                (cond ((symbolp x) x)
                      ((characterp x)
                       (intern (string x)))
                      ((rationalp x)
                       x)
                      ((string x)
                       (intern x))))
            (reverse out))))
  
;;;
;;; List lexer for strategies.
;;;

(defun strategy-lst-lexer (lst)
  #'(lambda ()
      (let ((value (pop lst)))
        (if (null value)
            (values nil nil)
          (let ((terminal
                 (cond ((member 
                         value 
                         '(+ - * / |(| |)| = > >= <= < ==> |/\\| |\\/| |~| |[|
                             |]| ^ /= != |,| IF BY APPLY RUN REPEAT THEN NL DIM
                             DEG BW |:=| |;| WHEN CID)) value)
                       ((integerp value) 'int)
                       ((rationalp value) 'rational)
                       ((symbolp value) 
                        (cond 
                         ((member value (avail-cmfs-sym)) 'cmf)
                         ((member value (cmf-args-all)) 'cs-arg)
                         ((member value (all-strats)) 'strategy-name)
                         (t (lex-error "[Lex-strategy] Unexpected symbol"))))
                       (t (lex-error "[Lex-strategy] Unexpected symbol" 
                                     :value value)))))
            (values terminal value))))))

;;;
;;; P-STRATEGY: Parse a RAHD strategy string into an S-expression.
;;;

(defun p-strategy (s)
  (let ((stls (strategy-str-to-lex-syms s)))
    (yacc:parse-with-lexer (strategy-lst-lexer stls)
                           strategy-parser)))
