;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Core prover interface routines.
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
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;;
;;; This file: began on         29-July-2008,
;;;            last updated on  14-December-2010.
;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; To Compile/Load:
;;;
;;;  :cload rahd
;;;  (rahd-reboot)
;;;
;;; Once loaded, to attempt to prove a goal automatically:
;;;
;;;  (g GOAL-IN-CNF) ; Install GOAL-IN-CNF as top-level goal (0).
;;;  (go!)           ; Invoke the waterfall upon GOAL-IN-CNF.
;;;
;;;
;;; To wipe your session and begin work on a new proof obligation without rebooting, 
;;; eval (r).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package RAHD)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *RAHD-DEBUG*: Set the debug flag.  Also, see: (WITH-RAHD-DEBUGGING ...).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *rahd-debug* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *RAHD-VERBOSITY*: Set the VERBOSITY level.  This determines how much live information
;;;  is printed out during proof search.  All calls to (FMT ...) are governed by this
;;;  value.
;;;
;;;   Key:   0   No output whatsoever during proof search,
;;;          1   Standard operation with information printed for every tactic that
;;;               made progress on the installed goal + a final report,
;;;          2   Enhanced version of 1 that prints the following characters during
;;;               tactic execution: 
;;;                                . - Tactic executed on a case in GOAL-SET and
;;;                                     no progress was made for that case,
;;;                                ! - Tactic executed on a case in GOAL-SET and
;;;                                     succeeded in refuting it,
;;;                                $ - Tactic executed on a case in GOAL-SET and
;;;                                     succeeded in reducing (but not refuting)
;;;                                     it,
;;;                                @ - Tactic executed on a case in GOAL-SET and
;;;                                     proved it was satisfiable, thus yielding 
;;;                                     a counter-example to the installed goal.
;;;
;;;          9  Proof debug mode.  Everything I've marked for possible printing that is of
;;;              direct relevance to proof search is printed.
;;;         10  System debug mode.  An enhancement of 9 that also prints information
;;;              pertaining to sys-calls (spawns, forks, and so on).
;;;
;;;  This verbosity level is cummulative, so that a setting of N causes all information
;;;  marked as level n (0 <= n <= N) to be printed (to *standard-output*).
;;;
;;;  Also, see: (WITH-RAHD-VERBOSITY n ...), (WRV n ...), (WRD ...).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *rahd-verbosity* 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *GOAL-STACK-KEYS*: the collection of goal-keys for members of the goal-stack.
;;;
;;;  A goal-key for a goal X is always either 0 (meaning X is the top-level goal), or of 
;;;   the form (PARENT-GOAL-KEY . CASE), which signifies that the waterfall spawned 
;;;   goal X while it was working on case CASE of the goal with key PARENT-GOAL-KEY, Y,
;;;   and if X is refuted, then case CASE of goal Y will be refuted.
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *goal-stack-keys* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *GOAL-STACK-DATA*: A hash-table for (sub)goal meta-data, key'd by goal-key.
;;;
;;; Each member of the *GOAL-STACK-DATA* hash-table is an array of size six:
;;;
;;;  key:goal-key   (goal-in-cnf   goal-set-size   goal-set-unknown-size   goal-set-max-dim
;;;                  goal-set-tactic-replay goal-set-local-interval-boxes goal-set-vt-bs)
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *goal-stack-data* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *GOAL-SETS*: A hash-table pairing each goal-key with its set of CTRs (cases to refute).
;;;
;;; Each member of the hash-table is an array with each element an array of the form:
;;;
;;;    (CASE-ID  CASE  STATUS  VT-BINDINGS)
;;;
;;; where CASE-ID is an array-index, CASE is a case to be refuted in CNF, and
;;; STATUS is either :UNKNOWN (must still be refuted) or :UNSAT (with a justification)
;;; or :SAT (possibly with a model assigning algebraic (currently rational) values to
;;; variables), and VT-BINDINGS is a list of (v tm) pairs (variable, term) which logs 
;;; substitutions that are reflected in the corresponding case.
;;;
;;; Note: The GOAL-SETS record for the current goal under question is bound to *GS*.
;;;
;;; Note: Once a new goal is installed, its GOAL-SET entry is nil until it is DRILLED-DOWN
;;;  using BUILD-GOAL-SET.  No tactics can be applied until BUILD-GOAL-SET has been run.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *goal-sets* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; CURRENT-GOAL-KEY: The key of the goal currently under focus.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *current-goal-key* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; ** LOCAL COPIES OF GOAL-STACK-DATA and GOAL-SET for CURRENT GOAL **
;;; 
;;; The following globals are swapped in and out when a user switches proof state
;;; between different active goals.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *G*: The current top-level goal in CNF.  This is to be refuted.
;;;      All variables are interpreted as being existentially quantified.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *g* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *GS*: The set of cases that must be each refuted in order
;;; to refute *g*.
;;;
;;; This is an array with each element an array of the form:
;;;
;;;    (CASE-ID  CASE  STATUS  VT-BINDINGS)
;;;
;;; where CASE-ID is an array-index, CASE is a case to be refuted in CNF,
;;; STATUS is either :UNKNOWN (must still be refuted) or :UNSAT (with a justification),
;;; and VT-BINDINGS is a list of (v tm) bindings logging the substitutions reflected
;;; in the corresponding case.
;;;
;;; We set the *GS* to nil until the user has installed a goal and DRILLED-DOWN
;;; to create the goal-set of cases.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *gs* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *GS-SIZE*: The total number of cases in *GS*.  Once a goal-set is
;;; built for a goal, this should never be changed.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *gs-size* 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; *GS-UNKNOWN-SIZE*: The total number of cases currently with status :UNKNOWN
;;; in the goal-set (e.g. these are the cases that still remain to be refuted or
;;; satisfied).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *gs-unknown-size* 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GS-MAX-DIM: The maximal dimension of the goals in the goal-set.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *gs-max-dim* 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; TACTIC-REPLAY: A list of the sequence of tactic invocations that have taken place
;;; during the current verification session.  This is reset everytime (G ...) is invoked.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *tactic-replay* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; LAST-TACTIC-MADE-PROGRESS: Did the last tactic evaluated make any progress?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *last-tactic-made-progress* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; LAST-TACTIC-PROGRESS-LST: What kind of progress did the last tactic make?
;;;
;;;   For F.Kirchner's Coq integration.  This is a list of the following shape,
;;;    consisting of entries for each case upon which the tactic made progress:
;;;     (:CASE-ID CASE-ID :FORMULA FORMULA :STATUS STATUS :GOAL-KEY GOAL-KEY :CMF CMF).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *last-tactic-progress-lst* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; I-BOXES-NUM-LOCAL: A hash-table mapping polynomials in Q[*VARS-TABLE*] into 
;;;  numerical interval boxes (e.g., connected subsets of (R \union {-inf, +inf})) with
;;;  endpoints in Q \union {-inf, +inf}.
;;;
;;; This is the local version that is maintained independently for each case.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *i-boxes-num-local* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GS-VT-BINDINGS: A list of variable bindings that the current GS context has already
;;;  used to perform substitutions of smaller terms for variables; these substitutions
;;;  are valid for all members of the current *GS*.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *gs-vt-bindings* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GLOBAL-VT-BINDINGS: A list of variable bindings that the current global context has
;;;  used to perform substitutions of smaller terms for variables; these substitutions
;;;  are valid for all members of all *GS*'s.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *global-vt-bindings* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; ** GLOBALS AVAILABLE TO ALL GOALS **
;;;
;;; The following globals are available to all goals.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; I-BOXES-NUM-GLOBAL: A hash-table mapping polynomials in Q[*VARS-TABLE*] into 
;;;  numerical interval boxes (e.g., connected subsets of (R \union {-inf, +inf})) with
;;;  endpoints in Q \union {-inf, +inf}.
;;;
;;; This is the global version that is valid for all cases and is derived from the 
;;;  top-level goal (before its DNF/case translation).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *i-boxes-num-global* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GBASIS-CACHE: A hash table for caching Groebner basis calculations across cases and
;;;  case revisions / subgoals.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *gbasis-cache* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; CANON-POLY-CACHE: A hash table for caching polynomial canonicalizations.  This should
;;;  be especially helpful for goals with large goal-sets.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *canon-poly-cache* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; STURM-SEQ-CACHE: A hash table for caching Sturm sequence computations.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *sturm-seq-cache* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SQR-FREE-CACHE: A hash table for caching square-free reductions of univariate polys.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *sqr-free-cache* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GBASIS-USE-COCOA: Should we use the CoCoA commutative algebra system to do Groebner
;;;  bases calculations (instead of our own internal routines)?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *gbasis-use-cocoa* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; CANON-POLY-USE-CACHE: Should we cache polynomial canonicalizations?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *canon-poly-use-cache* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; PROOF-ANALYSIS-CACHE: A hash table for caching information about the current proof.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *proof-analysis-cache* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; ENABLE-PROOF-ANALYSIS: Should proof analysis data be logged?
;;; ENABLE-PROOF-ANALYSIS-LATEX: Should a LaTeX-friendly table row be printed in the PA?
;;; ENABLE-QEPCAD: Should QEPCAD-B qe procedure be called externally?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *enable-proof-analysis* nil)
(defparameter *enable-proof-analysis-latex* nil)
(defparameter *enable-qepcad* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; DISABLE-GEN-CAD: Should generic CAD be disabled in waterfall invocations?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *disable-gen-cad* nil)
(defparameter *enable-rcr-svars* t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; EXACT-REAL-ARITH-USED: Was exact real arithmetic used in the current proof session?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *exact-real-arith-used* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; CURRENT-TACTIC-CASE: The current case in the current goal's goal-set being examined in 
;;; the MAP-CMF loop.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *current-tactic-case* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SAT-CASE-FOUND?: Has a SATisfiable case been found?  If so, then the entire installed
;;;  goal is satisfiable, and thus we can stop attempting to refute the remaining cases.
;;;
;;; SAT-MODEL: Have we constructed a counter-model satisfying one of the cases?  If so,
;;;  it is stored here.
;;;
;;; GOAL-REFUTED: Has the goal been refuted?  This may happen even before we have 
;;;  expanded into a goal-set by Phase I processing of the initial *G*.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *sat-case-found?* nil)
(defparameter *sat-model* nil)
(defparameter *goal-refuted?* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GB-MAX-STEPS: Maximal number of `steps' to take in GBasis construction calls.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *gb-max-steps* 1000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; NZ-TERMS: Terms that aren't allowed to be zero (because they were denominators).
;;;  This matters for potential SAT witnesses: If we have a proposed counter-model
;;;  with explicit algebraic number values for variables, we must make sure the
;;;  terms which appeared as denominators in the division formulation of the goal
;;;  are indeed non-zero.  For UNSAT goals, this doesn't matter.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *nz-terms* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; DIV-NZ-DENOMS: Should we conjoin non-zero conditions derived from denominators of 
;;;   all input formulae to the input formula?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *div-nz-denoms* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; RULE-SETS-TABLE: A table of available RAHD rulesets, indexed by ruleset name (symbol).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *rule-sets-table* (make-hash-table :test 'eq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; RULES-TABLE: A table of available RAHD rules, indexed by rule name (symbol).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *rules-table* (make-hash-table :test 'eq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; CAD-PFS-CACHE: A hash cache of projection factor sets computed during fd-cad.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *cad-pfs-cache* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; CAD-PFS-CACHE: A hash cache of rational sample points computed during fd-cad.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *cad-rsp-cache* (make-hash-table :test 'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; RESET-STATE: Reset entire (local and global) proof state.
;;; Note: if :keep-hashes is t, then we only reset local proof state.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rahd-reset-state (&key no-output keep-hashes)
  (when (not keep-hashes)
    (clrhash *gbasis-cache*)
    (clrhash *canon-poly-cache*)
    (clrhash *sqr-free-cache*)
    (clrhash *sturm-seq-cache*)
    (setq *goal-stack-keys* nil)
    (clrhash *goal-stack-data*)
    (clrhash *goal-sets*)
    (clrhash *proof-analysis-cache*)
    (clrhash *i-boxes-num-local*)
    (clrhash *i-boxes-num-global*)
    (clrhash *cad-pfs-cache*)
    (clrhash *cad-rsp-cache*))
  (setq *vars-table* nil)
  (setq *current-tactic-case* nil)
  (setq *global-vt-bindings* nil)
  (setq *goal-refuted?* nil)
  (setq *sat-case-found?* nil)
  (setq *sat-model* nil)
  (setq *nz-terms* nil)
  (setq *current-goal-key* nil)
  (setq *last-tactic-made-progress* nil)
  (setq *last-tactic-progress-lst* nil)
  (setq *tactic-replay* nil)
  (setq *exact-real-arith-used* nil)
  (setq *g* nil)
  (setq *gs* nil)
  (setq *gs-size* 0)
  (setq *gs-unknown-size* 0)
  (setq *gs-max-dim* 0)
  (setq *gs-vt-bindings* nil)
  (when (not no-output)
    (if keep-hashes (fmt 2 "~% Local goal state reset, but global structures unchanged.~%"
			 (fmt 2 "~% Full RAHD system state successfully reset.~%"))))
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SAVE-CURRENT-GOAL: Save the local data for the current goal in the
;;; GOAL-STACK-DATA and GOAL-SETS hash tables.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun save-current-goal (&optional no-output)
  (set-goal-stack-data *current-goal-key*
		       :goal-set-size *gs-size*
		       :goal-set-unknown-size *gs-unknown-size*
		       :goal-set-max-dim *gs-max-dim*
		       :goal-set-tactic-replay *tactic-replay*
		       :goal-set-last-tactic-progress-lst *last-tactic-progress-lst*
		       :goal-set-local-interval-boxes *i-boxes-num-local*
		       :goal-set-local-vt-bs *gs-vt-bindings*)
  (setf (gethash *current-goal-key* *goal-sets*) *gs*)
  (when (not no-output)
    (fmt 2 "~% Proof state for goal ~A has been saved." 
	 (format-goal-key *current-goal-key*)))
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; LOAD-GOAL: Load a goal from GOAL-STACK-DATA and GOAL-SETS into the active
;;; globals, so that it can be worked on tactically.
;;;
;;; Note: This does not change the order of GOAL-STACK-KEYS.
;;;       Also, this does not save the current state.  SAVE-CURRENT-GOAL should
;;;       be used for this (all wrapped together in SWAP-TO-GOAL).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun load-goal (goal-key &optional no-output)
  (multiple-value-bind 
   (goal-stack-record stack-rec-exists?)
   (gethash goal-key *goal-stack-data*)
   (if stack-rec-exists?
       (multiple-value-bind
	(goal-set-record set-rec-exists?)
	(gethash goal-key *goal-sets*)
	(if set-rec-exists?
	    (progn
	      
	      ;; Load GOAL-STACK data record

	      (setq *g* (aref goal-stack-record 0))
	      (setq *gs-size* (aref goal-stack-record 1))
	      (setq *gs-unknown-size* (aref goal-stack-record 2))
	      (setq *gs-max-dim* (aref goal-stack-record 3))
	      (setq *tactic-replay* (aref goal-stack-record 4))
	      (when (not (consp *tactic-replay*))
		(setq *tactic-replay* nil))
	      (setq *last-tactic-progress-lst* (aref goal-stack-record 5))
	      (setq *i-boxes-num-local* (aref goal-stack-record 6))
	      
	      ;; Load GOAL-SET record
	      
	      (setq *gs* goal-set-record)
	      
	      ;; Set the current GOAL-KEY reference
	      
	      (setq *current-goal-key* goal-key)
	      
	      ;; Synchronization complete
	      
	      (when (not no-output)
		(fmt 2 "~% Goal ~A loaded into local bindings."
		     goal-key))
	      t)
	  (break (error-string 'g-no-goal-to-load `(,goal-key ',*goal-stack-keys*)))))
	(break (error-string 'g-no-goal-to-load `(,goal-key ',*goal-stack-keys*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SWAP-TO-GOAL: Save the proof state for the current goal, then load the proof state
;;;  for the goal whose key is GOAL-KEY.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun swap-to-goal (goal-key &optional no-output)
  (save-current-goal no-output)
  (load-goal goal-key no-output)
  (when (not no-output)
    (fmt 2 "~% Goal ~A swapped in as the active goal." 
	 goal-key))
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; G: Install new current top-level goal.
;;;
;;; f: Goal in CNF to be added to goal-stack.
;;;
;;; Keyword parameters:
;;;  :goal-key     -- Key to assign to this goal.
;;;  :abandon-ok   -- Is it OK to abandon current proof session
;;;                    and start a new one?
;;;  :overwrite-ok -- Is it OK to overwrite the data of a goal 
;;;                    that already exists in the GOAL-STACK?
;;;  :vars-table   -- An explicit ordering of the variables 
;;;                    If an ordering isn't given, then we compute one (for goal 0) by
;;;                     (i) keeping the order in the current *vars-table* if nonempty,
;;;                    (ii) adding all variables appearing in f but not in *vars-table*
;;;                          at the end of vars-table, in the order they appear in f.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun g (f &key (goal-key 0) abandon-ok overwrite-ok vars-table)
  (if (not f) (break (error-string 'g-empty-goal)))
  (cond ((and (or *current-goal-key* *goal-stack-keys*)
	      (equal goal-key 0)
	      (not (or abandon-ok overwrite-ok)))
	 (break (error-string 'g-abandon)))
	((and (not (equal goal-key 0))
	      (member goal-key *goal-stack-keys*)
	      (not overwrite-ok))
	 (break (error-string 'g-overwrite `(,goal-key))))
	(t (if (or abandon-ok (not *goal-stack-keys*)) 

	       ;;
	       ;; Either the first goal of a session or the
	       ;; the first goal after the abandonment of a session,
	       ;; thus we reset the entire system state.
	       ;;

	       (rahd-reset-state) 

	     ;;
	     ;; Otherwise, we are adding a new goal on top of a 
	     ;; running session, so we save the current goal.
	     ;;

	     (save-current-goal))
	   (when (equal goal-key 0)
	     (setq *vars-table* (or vars-table (all-vars-in-cnf f))))
	   (if *goal-stack-keys* (rahd-reset-state :keep-hashes t))
	   (push goal-key *goal-stack-keys*)
	   (setq *goal-stack-keys* (remove-duplicates *goal-stack-keys*))
	   (setf (gethash goal-key *goal-stack-data*) (make-array 7))
	   (set-goal-stack-data goal-key :goal-in-cnf f)
	   (setq *g* f)
	   (setq *current-goal-key* goal-key)
	   (fmt 2 "~% Goal ~A installed and locally bound to *g*. ~%~%" 
		(format-goal-key goal-key))
	   t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SET-GOAL-STACK-DATA: 
;;;
;;;  (goal-key   <array: goal-in-cnf, goal-set-size, goal-set-unknown-size, goal-set-max-dim,
;;;      |               goal-set-tactic-replay, goal-set-last-tactic-progress-lst, 
;;;      |               goal-set-local-interval-boxes, goal-set-vt-bs>)
;;;      |
;;;   hash key for GOAL-STACK-DATA.
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun set-goal-stack-data (goal-key &key goal-in-cnf goal-set-size goal-set-unknown-size
				     goal-set-max-dim goal-set-tactic-replay
				     goal-set-last-tactic-progress-lst
			             goal-set-local-interval-boxes 
			             goal-set-local-vt-bs)
  (let ((goal-stack-record (gethash goal-key *goal-stack-data*)))
    (assert goal-stack-record)
    (if goal-in-cnf (setf (aref goal-stack-record 0) goal-in-cnf))
    (if goal-set-size (setf (aref goal-stack-record 1) goal-set-size))
    (if goal-set-unknown-size (setf (aref goal-stack-record 2) goal-set-unknown-size))
    (if goal-set-max-dim  (setf (aref goal-stack-record 3) goal-set-max-dim))
    (if goal-set-tactic-replay (setf (aref goal-stack-record 4) goal-set-tactic-replay))
    (if goal-set-last-tactic-progress-lst
	(setf (aref goal-stack-record 5) goal-set-last-tactic-progress-lst))
    (if goal-set-local-interval-boxes 
	(setf (aref goal-stack-record 6) goal-set-local-interval-boxes))
    (if goal-set-local-vt-bs
	(setf (aref goal-stack-record 7) goal-set-local-vt-bs))
  t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; BUILD-GOAL-SET: Build the goal-set of cases to refute for the top goal in goal-stack.
;;;
;;; Expanded with DIVISION support on 10-Dec-2008.
;;; Note that denominators are assumed to be checked for non-nullity (PVS guarantees this).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun build-goal-set (&key do-not-process-div keep-gbasis-cache)
  (let ((cs ;(subset-subsumption-gs
	     (drill-down 
	      (if do-not-process-div (expand-formula *g*)
		  (f-to-div-free-cnf-duc (expand-formula *g*))))))
    (setq *sat-case-found?* nil)
    (let ((num-cases (length cs)))
      (set-goal-stack-data *current-goal-key* 
			   :goal-set-size num-cases
			   :goal-set-unknown-size num-cases

			   ;;
			   ;; Note: We can inherit the global interval boxes
			   ;;  as a basis for interval contraction in the 
			   ;;  local context.
			   ;;

			   :goal-set-local-interval-boxes
			   (clone-i-boxes-for-cases 
			    *i-boxes-num-global*
			    num-cases))

      (setf (gethash *current-goal-key* *goal-sets*)
	    (make-array `(,num-cases 4)))
      (let ((gset (gethash *current-goal-key* *goal-sets*))
	    (i 0))
	(dolist (c cs)
	  (setf (aref gset i 0) i)
	  (setf (aref gset i 1) c)
	  (setf (aref gset i 2) '(:UNKNOWN))
	  (setf (aref gset i 3) nil)
	  (setq i (1+ i)))
	(setq *gs* gset))
      (when (not keep-gbasis-cache) (clrhash *gbasis-cache*))
      (setq *gs-unknown-size* num-cases)
      (setq *gs-size* num-cases)

      ;;;
      ;;; We only reset the proof-analysis-cache if we are building 
      ;;; the GS for a new top-level (key: 0) goal.
      ;;;

      (when (equal *current-goal-key* 0)
	(clrhash *proof-analysis-cache*))

      (fmt 2 "~% Goalset for goal ~A built and locally bound to *gs*." 
	   (format-goal-key *current-goal-key*))
      (prgs))))

(defun build-gs ()
  (build-goal-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; CREATE-SUBGOAL-AND-INVOKE-PROOF-PROC (f proc): A higher-order functional for making
;;;  recursive waterfall invocations.
;;;
;;; Given a formula f (in top-level CNF, just as the formulas passed to (G ...)), and a
;;; proof procedure that operates on the local proof state (such as #'waterfall, or #'go!),
;;; do the following:
;;;
;;;   (i) Save the current proof state (done by (G ...)),
;;;   (ii) Create a new subgoal for f, named `(,*current-goal-key* ,*current-tactic-case*),
;;;   (iii) Place this new subgoal on the top of the stack (done by (G ...)),
;;;   (iv) Build a goal-set for it,
;;;   (v) Invoke proc upon it,
;;;   (vi) Return t if #'proc refutes f, otherwise save the state of this
;;;        new subgoal and swap back to the parent goal (a user can then work on this
;;;        new subgoal interactively if desired).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun create-subgoal-and-invoke-proof-proc (f proc &key explicit-key)
  (let ((new-subgoal-key (or explicit-key `(,*current-goal-key* ,*current-tactic-case*)))
	(parent-goal-key *current-goal-key*)
	(vars-table *vars-table*))
    (g f :goal-key new-subgoal-key :overwrite-ok t)
    ;(build-gs) ;;; For now, we let PROC handle build-gs for us.
    (funcall proc)
    (let ((subgoal-refuted? (and (= *gs-unknown-size* 0)
                                 (not *sat-case-found?*))))
      (when parent-goal-key (swap-to-goal parent-goal-key))
      (setq *vars-table* vars-table)
      (if subgoal-refuted? t nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; ADD-NUM-BINDING: If a new substitution has been derived and applied (e.g.,
;;;  substituting a rational for a variable, or a term in other variables for a variable), 
;;;  then we store the binding in *active-vt-bindings*, expanding ground terms.
;;;
;;; Note: If this happens at the top-level, then we add the binding to the global list.
;;;  If this happens during a tactic call upon a case, then we add it to the VT-Bs list
;;;  of the case in *GS*.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun add-vt-binding (v tm)
  (let ((s (if (rationalp tm) tm
	       (if (term-ground? tm) (eval tm) tm))))
    (if *current-tactic-case*
	(setf (aref *gs* *current-tactic-case* 3)
	      (union (aref *gs* *current-tactic-case* 3)
		     (list (list v s))
                     :test 'equal))
	(setq *gs-vt-bindings*
	      (union *global-vt-bindings* (list (list v s))
                     :test 'equal)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GET-ACTIVE-VT-BINDINGS: Gather all known bindings used to eliminate
;;; variables in the current context.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-active-vt-bindings ()
  (let ((out (union *gs-vt-bindings* *global-vt-bindings* :test 'equal)))
    (when *current-tactic-case* 
      (setq out (union out (aref *gs* *current-tactic-case* 3))))
    out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; ** Tactics (mapped CMFs) **
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
      
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; CONTRA-EQS: Clear simply inconsistent goals.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun contra-eqs (&key case from to)
  (MAP-CMF #'simply-incons* 
           'CONTRA-EQS 
           "simple equality reasoning"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; DEMOD-NUM: Numerically demodulate goals.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun demod-num (&key case from to)
  (MAP-CMF #'demodulate-numerically
           'DEMOD-NUM
           "numerical demodulation"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SIMP-GLS: Simplify ground literals.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simp-gls (&key case from to)
  (MAP-CMF #'simplify-ground-lits
           'SIMP-GLS
           "ground literal simplification"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SIMP-TVS: Simplify truth values.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simp-tvs (&key case from to)
  (MAP-CMF #'remove-truth-vals*
           'SIMP-TVS
           "truth value simplification"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SIMP-ARITH: Simplify terms by simple polynomial arithmetic.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simp-arith (&key case from to)
  (MAP-CMF #'arith-simplify-case
           'SIMP-ARITH
           "arithmetic simplification"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; FERT-TSOS: Fertilize trivial sums of squares with PSD inequalities.
;;;  * This also finds an unsatisfiable witness if a conjunct is of the
;;;    form (< p 0) where p is a trivial square.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fert-tsos (&key case from to)
  (MAP-CMF #'fertilize-trivial-squares
           'FERT-TSOS
           "inequality fertilization for trivial sums of squares"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; UNIV-STURM-INEQS: Use univariate sturm theory to refute systems of univariate
;;; polynomial inequalities, provided that the single variable is constrained to
;;; take values in an explicitly given open interval.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun univ-sturm-ineqs (&key case from to)
  (MAP-CMF #'open-interval-univ-ineq
           'UNIV-STURM-INEQS
           "Sturm sequence analysis"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; OPEN-CAD: Use the EX-INF-MANY quantifier relaxation for open conjunctions via QEPCAD-B.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun open-ex-inf-cad (&key case from to)
  (MAP-CMF #'open-cad
           'OPEN-EX-INF-CAD
           "CAD with open relaxation via QEPCAD-B"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GEN-EX-CAD: Generic use of QEPCAD-B.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun gen-ex-cad (&key case from to)
  (MAP-CMF #'gen-cad
           'GEN-EX-CAD
           "generic CAD via QEPCAD-B"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; CANON-TMS: Canonicalize all terms.  This is more expensive than SIMP-ARITH, but
;;;  does much more.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun canon-tms (&key case from to)
  (MAP-CMF #'canonize-terms
           'CANON-TMS
           "polynomial canonicalization, arithmetic, and simplification"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; ZERO-RHS: Make the RHS of all non-stable formulas zero.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simp-zrhs (&key case from to)
  (MAP-CMF #'zero-rhs
           'SIMP-ZRHS
           "RHS zeroing with polynomial canonicalization"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; TRIV-IDEALS: Check for trivial ideals generated by equational constraints.
;;;              (this uses reduced Groebner bases.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun triv-ideals (&key case from to)
  (MAP-CMF #'trivial-ideal
           'TRIV-IDEALS
           "ideal triviality via reduced Groebner bases"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; RESIDUE-CLASS-RING-INEQS: Reduce all terms in strict inequalities to their
;;;  canonical representatives in the residue class ring induced by the
;;;  ideal generated by the equational constraints in the case.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun residue-class-ring-ineqs (&key case from to)
  (MAP-CMF #'ineqs-over-quotient-ring
           'RESIDUE-CLASS-RING-INEQS
           "residue class ring inequality term reduction"
           :case case :from from :to to))

(defun rcr-ineqs (&key case from to)
  (MAP-CMF #'ineqs-over-quotient-ring
           'RCR-INEQS
           "residue class ring inequality term reduction"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; OPEN-FRAG-EX-INF-CAD: Extract the strict inequalities from a constraint and check, 
;;;  via OPEN-EX-INF-CAD, if the resulting conjunction is :UNSAT over the reals.
;;;  
;;; Note: We cannot trust :SAT answers here, as equality constraints in the conjunction 
;;;  have been ignored.  The OPEN-FRAG-CAD function takes care of this and ignores them.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun open-frag-ex-inf-cad (&key case from to)
  (MAP-CMF #'open-frag-cad
           'OPEN-FRAG-EX-INF-CAD
           "open CAD"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SIMP-REAL-NULLSTELLENSATZ: Check to see if any equational constraint is an explicit real 
;;;  nullstellensatz refutation certificate.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simp-real-null (&key case from to)
  (MAP-CMF #'simp-real-nullstellensatz
           'SIMP-REAL-NULL
           "simple real nullstellensatz refutation"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; RESIDUE-CLASS-RING-FERT-SCALAR-VARS: Heuristically search to see if any indeteriminates 
;;;  in the residue class ring of a case are implied to be scalar valued in that ring.  
;;;  
;;;  We do this by examining a bounded sequence of powers of each residue class ring var-
;;;  iable, and using the fact that if the pth power of a variable v is a scalar c in a res-
;;;  idue class ring, then the variable v itself is equal to the pth root of c in the res-
;;;  idue class ring (and thus in the case being examined).  
;;;
;;;  In the case of c=0 for some v^k, it follows by the property that every RCF is an 
;;;  integral domain that v=0.  In the case of c=q for some v^k with q rational, we use 
;;;  exact real arithmetic to set v = (expt q 1/k) if k is odd, and to (+/-)(expt q 1/k) 
;;;  if k is even.  If k is even, we then recursively split on these two cases, placing them
;;;  on the goal-stack and invoking a new waterfall upon the subgoal (and its two cases) 
;;;  induced by the disjunction (MAP-CMF takes care of this by recognizing the :DISJ
;;;  disjunctive waterfall signifier).
;;;
;;;  If k is odd, then we just reduce the current case to the positive exact exponent
;;;  case mentioned above.
;;;
;;;  *** Note: We currently only do this when (expt q 1/k) is rational; irrational exact
;;;       real arithmetic support isn't yet complete.  
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rcr-svars (&key case from to)
  (MAP-CMF #'fertilize-scalar-vars-over-quotient-ring
           'RCR-SVARS
           "residue class ring power sequence to scalar reduction"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; INTEGRAL-DOMAIN-ZERO-PRODUCT-BRANCH: If any equations of the form (= (* A B) 0) for 
;;; any variables A,B in the polynomial ring exist, then we pick the first one and invoke
;;; a waterfall disjunction to branch upon (:OR (= A 0) (= B 0)).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun int-dom-zpb (&key case from to)
  (MAP-CMF #'integral-domain-zpb
           'INT-DOM-ZPB
           "integral domain zero product branching"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GENERAL-INTEGRAL-DOMAIN-ZERO-PRODUCT-BRANCH: An extension of the above INT-DOM-ZPB
;;; procedure for conjuncts of the form (= (* T_0 T_1) 0) for *arbitrary terms* T_0, T_1.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun int-dom-zpb-gen (&key case from to)
  (MAP-CMF #'integral-domain-zpb-gen
           'INT-DOM-ZPB-GEN
           "integral domain zero product branching"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; DERIVE-PARTIAL-DEMOD-LINS: Derive and apply partially linear demodulators.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun demod-lin (&key case from to)
  (MAP-CMF #'derive-partial-demod-lins
           'DEMOD-LIN
           "partial linear demodulation"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Interactive variable interval splitting:.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun interval-split (&key case from to tm pt)
  (MAP-CMF #'split-term-for-case
           'INTERVAL-SPLIT
           "variable interval splitting"
           :case case :from from :to to :tactic-params (list tm pt)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; INTERVAL-CP: Interval constraint propagation.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun interval-cp (&key case from to)
  (MAP-CMF #'icp-on-case
           'INTERVAL-CP
           "interval constraint propagation"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; SATURATE-ORIENT-LIN: Saturate a case with all linear orientations of its atoms.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun saturate-orient-lin (&key case from to)
  (MAP-CMF #'saturate-case-with-linear-orientations
           'SATURATE-ORIENT-LIN
           "saturation by all linear orientations"
           :case case :from from :to to))

(defun satur-lin (&key case from to)
  (MAP-CMF #'saturate-case-with-linear-orientations
           'SATUR-LIN
           "saturation by all linear orientations"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; FULL-GB-RNULL+ICP: Full GB search for Real Nullstellensatz witnesses using interval
;;;  constraint propagation upon slack variables. 
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun full-gbrni (&key case from to)
  (MAP-CMF #'full-gb-real-null-on-case
           'FULL-GBRNI
           "Real Nullstellensatz witness search (full GB + ICP)"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; BOUNDED-GB-RNULL+ICP: Bounded GB search for Real Nullstellensatz witnesses using 
;;;  interval constraint propagation upon slack variables. 
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bounded-gbrni (&key case from to gb-bound icp-period union-case summand-level)
  (MAP-CMF #'bounded-gb-real-null-on-case
           'bounded-gbrni
           "Real Nullstellensatz witness search (bounded GB + ICP)"
           :case case :from from :to to :tactic-params 
           (list gb-bound icp-period union-case summand-level)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; QUICK-SAT: Do a quick search for models (counter-examples) using bounds obtained 
;;;  through interval constraint propagation.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun quick-sat (&key case from to)
  (MAP-CMF #'qsi-on-case
           'quick-sat
           "Counter-example search using interval constraints"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; FACTOR-SIGN: Use multivariate factorisation to deduce signs of polynomials appearing
;;;  in literals, adjoining new literals expressing their signs when successful.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-sign (&key case from to)
  (MAP-CMF #'factor-sign-case
           'factor-sign
           "Sign determination by multivariate factorisation"
           :case case :from from :to to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; APPLY-RULESET: Saturate a case with the result of applying a ruleset.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun apply-ruleset (rs-name &key case from to)
  (MAP-CMF #'apply-ruleset-to-case
           'apply-ruleset
           "Apply a verified ruleset for forward-chaining"
           :case case :from from :to to :tactic-params 
           (list rs-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; FDEP-CAD: Full-dimensional extended partial CAD.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fdep-cad (&key case from to factor?)
  (MAP-CMF #'fdep-cad-on-case
           'fdep-cad
           "Full-dimensional extended partial cylindrical algebraic decomposition"
           :case case :from from :to to :tactic-params
           (list factor?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; STABLE-SIMP: A combination of the lightest arithmetical simplifiers that loops until
;;;  their composition reaches a fixed point w.r.t. *GS*.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun stable-simp ()
  (repeat-until-stable
   '(contra-eqs
     demod-num
     simp-gls
     simp-tvs
     simp-arith)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; UPDATE-STATUS: Check to see if a CMF returns a SAT/UNSAT statement, and update the
;;;  globals *goal-refuted?* and *sat-case-found?* accordingly.
;;;
;;;  FULL-SYS: Does this case represent the entire input system?  If so, then a :SAT
;;;   answer can be trusted.  Otherwise, it cannot.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun update-status (c fcn str full-sys?)
  (when (not (or *goal-refuted?* *sat-case-found?*))
    (fmt 1 " ~A" str)
    (let ((o (apply fcn (list c))))
      (cond ((equal (car o) ':UNSAT)
	     (setq *goal-refuted?* t))
	    ((and (equal (car o) ':SAT)
		  full-sys?) 
	     (setq *sat-case-found?* t))
	    (t nil)))
    (fmt 1 ".~%")))

;;;
;;; A phase-I rulesets tactic.
;;;

(defun phase-i-rulesets (c)
  (let ((c* (apply-ruleset-to-case c 'inequality-squeeze)))
    (if (not (equal c* c)) 
	(icp-on-case c*)
      c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; PHASE-I: Apply pre-processing to initial goal, before expanding to goal-sets.
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun phase-i (&key search-model)
  (declare (ignore search-model))
  (let ((unit-clauses 
	 (mapcar #'car (remove-if 
			#'(lambda (x) 
			    (or (> (length x) 1)
				(neg-lit? x)
				(div-formula?* (list x)))) *g*))))
    (let ((full-sys? (= (length *g*) (length unit-clauses))))
      (cond ((= (length unit-clauses) 0) (fmt 1 " No df-units.  Phase I aborted.~%"))
	    (t (update-status 
		unit-clauses #'icp-on-case "Contracting intervals" full-sys?)
	       (update-status
		unit-clauses #'phase-i-rulesets "Applying verified ruleset `inequality-squeeze.'\
 Contracting intervals" full-sys?))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; FP: Print status text at level 1 only if goal's status is unknown.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fp (str)
  (when (not (or *goal-refuted?* *sat-case-found?* (= *gs-unknown-size* 0)))
    (fmt 1 str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; WATERFALL: A heuristic procedure tying together the above tactics.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun waterfall (&key union-case search-model search-model* gbrn-depth
                       skip-cad skip-factor-sign)
  (when search-model
    (fp " Searching for trivial models.~%")
    (quick-sat))
  (fp " Contracting intervals.~%")
  (interval-cp)
  (fp " Applying simplifiers.~%")
  (simp-zrhs)
  (stable-simp)
  (demod-lin)
  (stable-simp)
  (simp-real-null)
  (fert-tsos)
  (univ-sturm-ineqs)
  (fp " Contracting intervals.~%")
  (interval-cp)
  (fp " Deriving additional linear constraints.~%")
  (satur-lin)
  (fp " Searching for real nullstellensatz interval obstructions.~%")
  (bounded-gbrni :union-case union-case :gb-bound gbrn-depth)
  (when (ruleset-enabled? 'inequality-squeeze)
    (fp " Applying verified ruleset `inequality-squeeze.'~%")
    (apply-ruleset 'inequality-squeeze)
    (fp " Applying verified ruleset `force-sign.'~%")
    (apply-ruleset 'force-sign))
  (fp " Contracting intervals.~%")
  (interval-cp)
  (fp " Examining ideal triviality.~%")
  (triv-ideals)
  (fp " Applying simplifiers.~%")
  (canon-tms)
  (stable-simp)
  (interval-cp)
  (fp " Injecting inequalities into induced quotient ring.~%")
  (rcr-ineqs)
  (stable-simp)
  (fert-tsos)
  (when *enable-rcr-svars*
    (rcr-svars))
  (stable-simp)
  (fp " Contracting intervals.~%")
  (interval-cp)
  (when (not skip-factor-sign)
    (fp " Computing multivariate factorisations and deducing signs.~%")
    (factor-sign))
  (simp-zrhs)
  (when (ruleset-enabled? 'inequality-squeeze)
    (fp " Applying verified ruleset `inequality-squeeze.'~%")
    (apply-ruleset 'inequality-squeeze)
    (fp " Applying verified ruleset `force-sign.'~%")
    (apply-ruleset 'force-sign))
  (fp " Contracting intervals.~%")
  (interval-cp)  
  (fp " Searching for real nullstellensatz interval obstructions.~%")
  (bounded-gbrni :union-case union-case :gb-bound gbrn-depth)
  (fp " Contracting intervals.~%")
  (interval-cp)
  (fp " Searching for zero-products.~%")
  (int-dom-zpb)
  (when (or search-model search-model*)
    (fp " Searching for trivial models.~%")
    (quick-sat))
  (fp " Injecting inequalities into induced quotient ring.~%")
  (rcr-ineqs)
  (when (not skip-cad)
    (fp " Performing full-dimensional cylindrical algebraic decomposition.~%")
    (fdep-cad))
  (when (or search-model search-model*)
    (fp " Searching for trivial models.~%")
    (quick-sat))
  (if (= *gs-unknown-size* 0) t nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GO!: A top-level waterfall invoker.
;;; 
;;; Keywords:
;;;
;;;  :TACTIC-REPLAY l, where l is a list of tactics that will be applied in order,
;;;  :DO-NOT-REBUILD-GS t, causes the goal-set to not be rebuilt,
;;;  :DO-NOT-RESET-CPC t, causes the canonicalized poly cache to not be reset.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun go! (&key tactic-replay do-not-reset-tactic-replay do-not-rebuild-gs
		 do-not-reset-cpc verbosity union-case search-model search-model*
		 vars-table gbrn-depth skip-cad skip-factor-sign)
  (if (not *G*) (fmt 0 "~%~% *** No goal installed.  See :DOC G. ~%~%")
    (let ((*rahd-verbosity* (if verbosity verbosity *rahd-verbosity*))
	  (start-time (get-internal-real-time)))
      (setq *current-tactic-case* nil)

      (fmt 1 "[Phase I]~%")
      (phase-i)

      (cond (*goal-refuted?* (fmt 1 " Real solution set empty.~%"))
	    (*sat-case-found?* (fmt 1 " Real solution set non-empty.~%"))
	    (t
	     (fmt 1 "~%[Phase II]~%")
	     (fmt 1 " Building DNF.~%")
	     (when (not do-not-rebuild-gs) 
	       (build-goal-set 
		:do-not-process-div 
		(if (not (equal *current-goal-key* 0)) t nil))
	       (setq *vars-table* (or vars-table (all-vars-in-cnf *g*))))
	     (when (and *canon-poly-use-cache* (not do-not-reset-cpc))
	       (clrhash *canon-poly-cache*))
	     (setq *exact-real-arith-used* nil)
	     (when (not do-not-reset-tactic-replay) (ctr))
	     (if tactic-replay
		 (mapcar #'(lambda (tactic) (eval `(,tactic))) tactic-replay)
	       (waterfall :union-case union-case :search-model search-model
			  :search-model* search-model* :gbrn-depth gbrn-depth
                          :skip-cad skip-cad :skip-factor-sign skip-factor-sign))))
      
      (let ((goal-proved-by-waterfall? (not (extract-non-refuted-cases))))

	(fmt 2 (if goal-proved-by-waterfall?
		   "~% Goal ~A proved (~D sec).~%"
		   "~% Goal ~A run complete (~A sec): ~D.~%")
	     (format-goal-key *current-goal-key*)
	     (float (/ (- (get-internal-real-time) start-time) internal-time-units-per-second))
	     (if *sat-case-found?* "counter-example found" 
		 (format nil "~A of ~A unrefuted cases remain" *gs-unknown-size* *gs-size*)))

	(fmt 3 "~% Goal ~A tactic replay: ~A.~%"
	     (format-goal-key *current-goal-key*)
	     (tactic-replay))
	  
	;;
	;; Only print " *** Theorem (GOAL ...) Proved *** " for the top-level goal, 0.
	;;
	  
	(when (equal *current-goal-key* 0) (prgs))
	(or goal-proved-by-waterfall? *goal-refuted?*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; REPEAT-UNTIL-STABLE: Given a sequence of tactics (given as a list), repeat their 
;;;  execution until the proof state is stable under their execution.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun repeat-until-stable (tactics &key case from to)
  (let ((last-tactic-made-progress? t))
    (while (and last-tactic-made-progress?
		(not *sat-case-found?*))
      (setq last-tactic-made-progress? nil)
      (dolist (tac tactics)
	(eval `(,tac :case ,case :from ,from :to ,to))
	(when (and (not last-tactic-made-progress?)
		   *last-tactic-made-progress*)
	  (setq last-tactic-made-progress? t))))
  t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; MAP-CMF: Map a CMF across the open cases of a goal.
;;;
;;; fcn-case-manip : a case manipulation function
;;; fcn-symbol     : a pretty printable name for fcn-case-manip, used both
;;;                  in printing and in justification.  This must be a symbol.
;;; fcn-desc       : a nice operational description of the tactic.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun MAP-CMF (fcn-case-manip fcn-symbol fcn-desc &key case from to tactic-params)
  (declare (ignorable fcn-desc))
  (setq *last-tactic-progress-lst* nil)
  (cond ((= *gs-unknown-size* 0) (progn (setq *last-tactic-made-progress* nil) t))
	(*sat-case-found?* nil)
	(t (let* ((num-changed 0)
		  (num-refuted 0)
		  (num-satisfied 0)
		  (start-time (get-internal-real-time))
		  (case-lb* (if case case (if from from 0)))
		  (case-ub* (if case case (if to to (1- *gs-size*))))
		  (case-lb (max case-lb* 0))
		  (case-ub (min case-ub* (1- *gs-size*)))
		  (fcn-str (format nil "~(~a~)" (symbol-name fcn-symbol))))
	     (when (or case from to) 
	       (fmt 3 "~% Thanks for the hint!  ~A is being applied only to cases in the range [~D..~D]." 
		    fcn-str case-lb case-ub))
	     (loop for i from case-lb to case-ub while (not *sat-case-found?*) do
		   (setq *current-tactic-case* i) ; Used for naming spawned subgoals.
		   (let ((c        (aref *gs* i 1))
			 (c-status (aref *gs* i 2)))
		     (if (equal (car c-status) ':UNKNOWN)
			 (if (not c) 

			     ;;
			     ;; The current case has been reduced to an empty conjunction 
			     ;; -- an implicit t -- Thus, we've found a counter-example.
			     ;;

			     (setf (aref *gs* i 2) `(:SAT :CASE-REDUCED-TO-EMPTY-CONJUNCTION ,(cdr c-status)))
			   (let ((fcn-result (if (not tactic-params)
						 (funcall fcn-case-manip c)
					       (apply fcn-case-manip `(,c ,@tactic-params)))))
			     (if (not (equal c fcn-result)) ; The current tactic actually did something.
				 (if (consp fcn-result)
				     (case (car fcn-result)

				       (:UNSAT 
					(setf (aref *gs* i 2)
					      `(:UNSAT ,(append (cdr c-status) (cons fcn-symbol (cdr fcn-result)))))
					(setq num-refuted (1+ num-refuted))
					(setq *last-tactic-progress-lst* 
					      (cons `(:CASE-ID ,i :STATUS :UNSAT :CMF ,fcn-symbol)
						    *last-tactic-progress-lst*))
					(fmt 7 "!"))
				       
				       (:SAT 
					(setf (aref *gs* i 2)
					      `(:SAT nil ,(append (cdr c-status) (cons fcn-symbol (cdr fcn-result)))))
					(fmt 2 "~% *** Counter-example found: Case ~D of goal ~A is satisfiable *** ~%"
					     i (format-goal-key *current-goal-key*))
					(setq num-satisfied (1+ num-satisfied))
					(setq *last-tactic-progress-lst*
					      (cons `(:CASE-ID ,i :STATUS :SAT :CMF ,fcn-symbol)
						    *last-tactic-progress-lst*))
					(fmt 7 "@")

					;; 
					;; Try to extract a SAT witness from variable bindings, if it
					;; has been implicitly constructed.
					;;

					(when (not *sat-model*)
					  (let* ((var-bindings (aref *gs* i 3))
						 (candidate-model 
                                                  `(:SAT (:MODEL ,var-bindings))))
					    ;;
					    ;; Now, let's check we really have a model.
					    ;;
					    
					    ;(when (eval-c c var-bindings)
					      (setq *sat-model* candidate-model)))

					(setq *sat-case-found?* (list *current-goal-key* i)))

				       (:DISJ
					(let ((new-subgoal-key `(,*current-goal-key* ,i))
					      (new-subgoal-formula (waterfall-disj-to-cnf (cdr fcn-result))))
					  (setf (aref *gs* i 2) `((:UNKNOWN-WITH-SPAWNED-SUBGOAL ,new-subgoal-key) 
								  ,(append (cdr c-status) `(,fcn-symbol))))
					  (fmt 3 "~% W\/: Spawning subgoal ~A as a sufficient condition for case ~A of goal ~A.~%"
					       (format-goal-key new-subgoal-key) 
					       i
					       (format-goal-key *current-goal-key*))
					  (let ((result-of-waterfall-on-subgoal
						 (create-subgoal-and-invoke-proof-proc new-subgoal-formula
										       #'go!
										       :explicit-key new-subgoal-key)))
					    (if result-of-waterfall-on-subgoal
						(progn
						  (fmt 3 "~% W\/: Subgoal ~A for goal ~A discharged, thus discharging case ~A of goal ~A.~%"
						       (format-goal-key new-subgoal-key) 
						       (format-goal-key *current-goal-key*)
						       i
						       (format-goal-key *current-goal-key*))
						  (setq num-refuted (1+ num-refuted))
						  (setf (aref *gs* i 2)
							`(:UNSAT :DISCHARGED-BY-SUBGOAL ,new-subgoal-key
								 ,(append (cdr c-status) (cons fcn-symbol (list (cdr fcn-result))))))
						  (setq *last-tactic-progress-lst* 
							(cons `(:CASE-ID ,i :STATUS (:UNSAT :DISCHARGED-BY-SUBGOAL) :CMF ,fcn-symbol)
							      *last-tactic-progress-lst*)))
					      
					      ;;
					      ;; If the subgoal isn't automatically discharged, we'll just leave it for the user to attack manually,
					      ;; and we will leave the formula for the current case unchanged.
					      ;;

					      (setq fcn-result c)

					      ))))
					  
				       (otherwise 
					(setf (aref *gs* i 1) fcn-result)
					(setf (aref *gs* i 2) (append c-status `(,fcn-symbol)))
					(setq num-changed (1+ num-changed))
					(setq *last-tactic-progress-lst*
					      (cons `(:CASE-ID ,i :STATUS :UNKNOWN :CMF ,fcn-symbol)
						    *last-tactic-progress-lst*))
					(fmt 7 "$"))))

			       ;;; Tactic execution on case i did nothing, so we print `.' at verbosity level 2.

			       (fmt 7 ".")))))))
	     
	     (setq *current-tactic-case* nil)
	     (if (or (> num-changed 0) (> num-refuted 0) *sat-case-found?*)
		 (progn 
		   (setq *last-tactic-made-progress* t)
		   (setq *tactic-replay* (cons `(,fcn-symbol ,@tactic-params) *tactic-replay*))
		   (setq *gs-unknown-size* (- *gs-unknown-size* (+ num-refuted num-satisfied)))
		   (let ((tactic-time (float (/ (- (get-internal-real-time) start-time) internal-time-units-per-second))))

		     (when *enable-proof-analysis* 
		       (let* ((cur-tactic-pa-rec (gethash fcn-symbol *proof-analysis-cache*))
			      (cur-tactic-count (when cur-tactic-pa-rec (car cur-tactic-pa-rec)))
			      (cur-tactic-time (when cur-tactic-pa-rec (cadr cur-tactic-pa-rec))))
		       (setf (gethash fcn-symbol *proof-analysis-cache*)
			     (list (+ num-changed num-refuted (or cur-tactic-count 0))
				   (+ tactic-time (or cur-tactic-time 0))))))

		     (case (not *sat-case-found?*)
			   (nil (fmt 2 "~%   ~D: Satisfiable case has been found.  Goal is not refutable." fcn-symbol))
			   (otherwise
			    (fmt 2 "   ~17A: [~4d refuted, ~4d reduced] ~4d ~A (~7d sec).~%" 
				 fcn-str num-refuted num-changed *gs-unknown-size* 
				 (if (= *gs-unknown-size* 1) "case remains" "cases remain") 
				 tactic-time)))

		     ;(prgs)
		     ))
	       (progn 
		 (setq *last-tactic-made-progress* nil)
		 (fmt 8 "~%   Tactic executed but did not make progress: ~A.~%" fcn-str)
		 t))
	     (when (or (= *gs-unknown-size* 0) *sat-case-found?*) t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; PUG: Print :UNKNOWN cases reamining in GOAL-SET.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pug (&key bound case)
  (if (and (> *gs-unknown-size* 0) (not *sat-case-found?*))
      (progn 
        (if case (fmt 0 "~% Printing case ~A for goal ~A.~%" case *current-goal-key*)
          (fmt 0 "~% Printing ~A of the open ~A cases for goal ~A.~%" 
               (if (not bound) "all" (format nil "the first ~R" bound)) *gs-unknown-size* *current-goal-key*))
	(fmt 0 "~% -------     -------------------------------------------------------------------")
	(fmt 0 "~% case-id     case")
	(fmt 0 "~% -------     -------------------------------------------------------------------~%")
	(let ((num-printed 1))
	  (dotimes (i *gs-size*)
	    (let ((c-id     (aref *gs* i 0))
		  (c        (aref *gs* i 1))
		  (c-status (aref *gs* i 2)))
	      (if (and (or (equal (car c-status) ':UNKNOWN)
			   (and (consp (car c-status))
				(equal (caar c-status) ':UNKNOWN-WITH-SPAWNED-SUBGOAL)))
		       (or (not bound)
			   (<= num-printed bound))
		       (or (not case)
			   (= i case)))
		  (progn (fmt 0 "~% ~7D     ~D    ~D ~%" 
			      c-id 
			      c
			      c-status)
			 (setq num-printed (1+ num-printed)))
		t))))))

  ;; If a user invokes (PUG) at any verbosity level, it's clear we should visibly (PRGS).
  ;; So, we dynamically bind *RAHD-VERBOSITY* to 1 for the call below.

  (let ((*rahd-verbosity* 2)) (prgs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; Print remaing goals status (done at the end of every tactic output).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun prgs ()
  (cond ((equal *g* nil)
	 (fmt 2 "~%~% No goal is currently installed.  Use (g <goal-in-cnf>).~%~%"))
	((and (<= *gs-size* 0) (not *goal-refuted?*))
	 (fmt 2 "~%~% No cases installed in goalset (*gs*).  Use (b).~%~%"))
	(*sat-case-found?*
	 (fmt 2 "~%~% Counter-example found.  Installed goal SAT, so unrefutable. ~%~%"))
	(t (fmt 2 "~%~% ~6D ~A in goalset (goal ~A) awaiting refutation. ~%~%" 
		*gs-unknown-size*
		(if (= *gs-unknown-size* 1) "case" "cases")
		*current-goal-key*)
	   (when (or (= *gs-unknown-size* 0) *goal-refuted?*)
	     (if (equal *current-goal-key* 0)
		 (fmt 2 "~% Q.E.D.  Theorem proved.~%~%")
	       (fmt 2 "~% .:. Goal ~A proved.~%~%" 
		    (format-goal-key *current-goal-key*))))))
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Print the tactic replay of the current session.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun tactic-replay ()
  (reverse *tactic-replay*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Extract non-refuted goals (both those marked `:UNKNOWN' or `:SAT') together with 
;;; their possible witnesses in the following form:
;;;
;;;     `(  (FORMULA_i  WITNESS_i) ).
;;;
;;; This is for PVS integration.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun extract-non-refuted-cases ()
  (let ((nrc-lst nil))
    (dotimes (i *gs-size*)
      (let ((c        (aref *gs* i 1))
	    (c-status (aref *gs* i 2)))
	(let ((c-mark (car c-status)))
	  (if (or (eq c-mark ':UNKNOWN)
		  (eq c-mark ':SAT)
		  (and (consp c-mark)
		       (eq (car c-mark) ':UNKNOWN-WITH-SPAWNED-SUBGOAL)))
	      (let ((nrc-case
		     (cons c (if (equal c-mark ':SAT) (cadr c-status) nil))))
		(setq nrc-lst (cons nrc-case nrc-lst)))))))
    nrc-lst))

;;;
;;; TRY-TO-PROVE: Given a top-level RAHD formula F and a goal name, G, try to prove F,
;;;  binding the proof attempt to goal-key G.  If we succeed, we return T. 
;;;  Otherwise, we return NIL.
;;;

(defun try-to-prove (f goal-key)
  (create-subgoal-and-invoke-proof-proc 
   f 
   #'go! 
   :explicit-key goal-key))

;;;
;;; CURRENT-STATS: Give some basic info about where the system currently is
;;;  within a proof tree.
;;;

(defun current-stats (&key show-goal)
  (when show-goal
    (fmt 0 "~% Goal: ~A,~%" *g*))
  (when *current-goal-key* 
    (when (or (equal *current-goal-key* 0)
              (consp *current-goal-key*))
      (if (equal *current-goal-key* 0)
          (cond (*gs*
                 (fmt 0 "~% Goalkey: ~A,~% Unknown cases: ~A of ~A.~%~%"
                      *current-goal-key*
                      *gs-unknown-size*
                      *gs-size*))
                ((not (or *sat-case-found?* *goal-refuted?*))
                 (fmt 0 "~% Goalkey: ~A.~% Goalset not built (use (b)).~%~%" 
                      *current-goal-key*)))
        (multiple-value-bind 
            (parent-data p-exists?)
            (gethash (car *current-goal-key*) *goal-stack-data*)
          (declare (ignore p-exists?))
          (fmt 0 "~% Goalkey: ~A,~% Unknown cases: ~A of ~A,~% Parent: ~A,~% Parent unknown cases: ~A of ~A.~%~%"
               *current-goal-key*
               *gs-unknown-size*
               *gs-size*
               (car *current-goal-key*)
               (aref parent-data 2)
               (aref parent-data 1)))))
  (cond ((and (not *sat-case-found?*) (or (and *gs* (= *gs-unknown-size* 0)) *goal-refuted?*))
	 (fmt 0 " Decision: unsat (proven).~%~%"))
	(*sat-case-found?* 
	 (fmt 0 " Decision: sat (disproven).~%~%~A~%" (format-model *sat-model*)))
	(t (fmt 0 " Goal status unknown.~%~%"))))
  t)

;;;
;;; UP: Go up to parent goal, updating the status of the corresponding
;;;  parent's case if the child subgoal has been refuted.
;;;

(defun up ()
  (if (consp *current-goal-key*)
      
      ;; 
      ;; Before walking up, let's see if our goal has already
      ;;  been refuted.  If so, we'll trickle the result up
      ;;  to our parent.
      ;;

      (progn
	(when (= *gs-unknown-size* 0)
	  (let ((parent-key (car *current-goal-key*))
		(child-gs-idx (cadr *current-goal-key*)))	    
	    (multiple-value-bind
		  (parent-gs p-exists?)
		  (gethash parent-key *goal-sets*)
		  (declare (ignore p-exists?))
	      (let ((known-child-status 
		     (aref parent-gs child-gs-idx 2)))
		(fmt 9 "~%[UP] Known status from above: ~A~%"
		     known-child-status)
		(when (not (equal (car known-child-status)
				  ':UNSAT))  
		  
		  ;;
		  ;; At this point, the child has been refuted, so the parent's
		  ;;  case who spawned it needs to be updated to reflect this.
		  ;; * We also need to adjust the total number of unknown cases
		  ;;   remaining for the parent.
		  ;;

		  (setf (aref parent-gs child-gs-idx 2)
			`(:UNSAT :DISCHARGED-BY-SUBGOAL ,*current-goal-key*
			  ,(append (cdr known-child-status))))

		  (multiple-value-bind
		      (parent-gs-data p-gs-exists?)
		      (gethash parent-key *goal-stack-data*)
		      (declare (ignore p-gs-exists?))
		    (setf (aref parent-gs-data 2) 
			  (1- (aref parent-gs-data 2))))
		    
		  (fmt 1 "~% Trickled refutation up to Case ~A of Goal ~A.~%"
		       child-gs-idx parent-key))))))
      
	(swap-to-goal (car *current-goal-key*)))

    (fmt 0 "~% You are already at the root goal. ~%"))
  t)

;;;
;;; E: Execute a sequence of tactics.
;;;

(defmacro e (&rest rst)
  (dolist (tac rst)
    (if (not (consp tac))
	(funcall tac)
	(let ((params (cdr tac)))
	  (apply (car tac) params))))
  t)

;;;
;;; CHECK: Front-end ``unsat'' or ``unknown'' function.
;;;

(defun check (f &key verbosity print-model search-model search-model*
		gbrn-depth from-repl skip-cad skip-factor-sign)
  (cond 
   ((top-level-syntax-check f)
    (let ((*rahd-verbosity* 
	   (if (rationalp verbosity) verbosity 1)))
      (when *current-goal-key* (r))
      (g f)
      (let ((result (go! :search-model search-model
			 :search-model* search-model*
			 :gbrn-depth gbrn-depth
                         :skip-cad skip-cad
                         :skip-factor-sign skip-factor-sign)))
	(fmt 1 "~%[Decision]")
	(fmt 0 "~%")
	(cond (result (if from-repl "unsat." " unsat~%"))
	      (*sat-case-found?* 
	       (format nil (if from-repl "sat.~A"
                             " sat~A~%")
		       (if (and print-model *sat-model*)
			   (format nil "~%~A~%" 
				   (format-model *sat-model*))
			   "")))
	      (t (if from-repl "unknown." " unknown~%"))))))
   (t (if from-repl "formula syntax error." "~%formula syntax error~%"))))

;;;
;;; CL-FIND-OPTION: Given a flag string, return an MV of
;;;  the form (option-given? option-value).
;;;
;;; Arg? should be true if flag f has a parameter, such
;;;  as `-formula X.'  If arg? is false, then our MV
;;;  returns (T . NIL) to mean simply that the flag was
;;;  found.
;;;

(defun cl-find-option (f opts arg?)
  (cond ((endp opts) (values nil nil))
	((equal (read-from-string (car opts)) f)
	 (cond ((not arg?) (values t nil))
	       (t (if (consp (cdr opts))
		      (values t (read-from-string (cadr opts)))
		      (values nil f)))))
	(t (cl-find-option f (cdr opts) arg?))))

;;;
;;; RAHD-CL-CHECK: Command-line version of CHECK that accepts
;;;  an S-expression RAHD formula.
;;;

(defun rahd-cl-check ()
  (in-package rahd)
  (let ((opts #+ccl ccl:*command-line-argument-list* 
	      #+sbcl sb-ext:*posix-argv*))
    (multiple-value-bind (formula-given? formula)
	(cl-find-option '-FORMULA opts t)
      (multiple-value-bind (verbosity-given? verbosity)
	  (cl-find-option '-VERBOSITY opts t)
	(multiple-value-bind (gbrn-depth-given? gbrn-depth)
	    (cl-find-option '-GBRN-DEPTH opts t)
	  (declare (ignorable verbosity-given? gbrn-depth-given?))
	  (let ((print-model? (cl-find-option '-PRINT-MODEL opts nil))
		(search-model? (cl-find-option '-SEARCH-MODEL opts nil))
		(search-model*? (cl-find-option '-SEARCH-MODEL! opts nil))
		(regression? (cl-find-option '-REGRESSION opts nil))
		(div-nz-denoms? (cl-find-option '-DIV-NZ-DENOMS opts nil))
                (interactive? (cl-find-option '-I opts nil))
                (ip-evaluator? (cl-find-option '-IP opts nil)))
	    (when (and (not ip-evaluator?) 
                       (or (not formula-given?) 
                           (or (not verbosity)
                               (and (rationalp verbosity) (>= verbosity 1)))))
	      (progn
		(fmt 0 "
RAHD: Real Algebra in High Dimensions ~A
 designed and programmed by grant o. passmore {g.o.passmore@sms.ed.ac.uk}
  with intellectual contributions from p.b.jackson, b.boyer, g.collins, 
  h.hong, f.kirchner, j moore, l.de moura, s.owre, n.shankar, a.tiwari,
  v.weispfenning and many others.  This version of RAHD is using Maxima 
  multivariate factorisation & SARAG subresultant PRS + Bernstein bases.~%~%" 
		     *rahd-version*)
		(when (and (not formula-given?) (not interactive?)
                           (not ip-evaluator?))
		  (fmt 0 
" Error: No formula given.

 Usage: ~A -formula \"RAHD formula\" <options>
  with options:

    -verbosity q      (0<=q<=10)     degree of proof search output (def: 1)
    -search-model                    search for counter-models
    -search-model!                   search for counter-models, but only
                                      after refutation cycle
    -fdep-cad $                      full-dimensional extended partial
                                      cylindrical algebraic decomposition
    -quad-vts $                      quadratic virtual term substitution
    -muchnik-qe $                    Muchnik full quantifier elimination
    -phase-i $                       phase i proof search
    -phase-ii $                      phase ii proof search
    -div-nz-denoms                   automatically conjoin constraints stating
                                      input formula denominators are non-zero
    -rri %                           method for real root isolation
    -rri-only                        only perform real root isolation
    -rri-epsilon q                   maximum width of open real root 
                                      isolation intervals (def: 1)
    -gbrn-depth n                    depth of GB real nullstellensatz search
    -crb-quotient q                  quotient base for refining Cauchy root
                                      bounds (def: 1000)
    -smsp-base q                     sample-point selection base for
                                      counter-model search (def: 10)
    -refine-crb                      refine Cauchy root bounds before
                                      performing real root isolation
    -gb-sat-disc                     perform discriminant saturation during
                                      GB-based real Nullstellensatz search
    -cmf-exec #                      execute only a given list of cmfs
    -print-model                     print a counter-model, if found
    -print-tactics                   print a tactic replay of proof search
    -print-failure                   if a decision is not reached, print 
                                      a failure report (unrefuted cases)
    -regression                      run regression suite for testing build
    -i                               (human-oriented) interactive shell
    -ip                              (machine-oriented) formula evaluator

  where n is a natural, q is a rational presented as `a/b' or `a' for integers a,b,
        $ is either `on', `off' or `only' (def: `on'), 
        % is either `sturm' or `bernstein' (def: `sturm'),
        # is a list of the form \"(cmf1 cmf2 ... cmfn)\" of RAHD cmfs.~%"

    (car opts)))))
	    (cond (regression? (wrv (if (rationalp verbosity) verbosity 1) 
				    (rahd-regression-suite)))
                  (interactive? (r-repl))
                  (ip-evaluator? (p-repl))
		  (formula-given?
		   (when div-nz-denoms?
		     (setq *div-nz-denoms* t))
		   (fmt 0 (check formula 
			      :verbosity (when (rationalp verbosity)
					   (min verbosity 10))
			      :print-model print-model?
			      :search-model search-model?
			      :search-model* search-model*?
			      :gbrn-depth gbrn-depth))))
	    (fmt 0 "~%")))))))


;
;    -verify-and-extend f             verify a proof strategy (possibly with rulesets)
;                                      and build a new RAHD binary including it
;    -use-strategy s                  use a user-defined strategy for proving formula
;    -list-strategies                 list all built-in verified proof strategies"
;
;        f is a filename, and s is the name of a known verified proof strategy.~%