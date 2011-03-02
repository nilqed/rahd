;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Core general prover data structures and functions.
;;;
;;;   (in old versions of RAHD, before the proof strategy machinery,
;;;      the ancestor of this file was known as "prover.lisp")
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
;;; This file: began on         29-July-2008           (as "prover.lisp"),
;;;            last updated on  18-February-2011.
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
	 *current-goal-key*))
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
;	   (fmt 2 "~% Goal ~A installed and locally bound to *g*. ~%~%" 
;		goal-key)
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

(defun build-goal-set (&key do-not-process-div keep-gbasis-cache do-not-split-ineqs?)
  (let ((cs (if (eq (car *g*) ':CASES)
		(cdr *g*)
	      (drill-down 
	       (if do-not-process-div 
		   (expand-formula *g* 
				   :do-not-split-ineqs? do-not-split-ineqs?)
		 (f-to-div-free-cnf-duc (expand-formula *g*
							:do-not-split-ineqs?
							do-not-split-ineqs?)))))))
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
	   *current-goal-key*)
      (prgs))))

(defun build-gs (&key do-not-split-ineqs?)
  (build-goal-set :do-not-split-ineqs? do-not-split-ineqs?))

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
		    *current-goal-key*)))))
  t)

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
                      (format-goal-key *current-goal-key*)
                      *gs-unknown-size*
                      *gs-size*))
                ((not (or *sat-case-found?* *goal-refuted?*))
                 (fmt 0 "~% Goalkey: ~A.~% Goalset not built (use (b)).~%~%" 
                      (format-goal-key *current-goal-key*))))
        (multiple-value-bind 
            (parent-data p-exists?)
            (gethash (car *current-goal-key*) *goal-stack-data*)
          (declare (ignore p-exists?))
          (fmt 0 "~% Goalkey: ~A,~% Unknown cases: ~A of ~A,~% Parent: ~A,~% Parent unknown cases: ~A of ~A.~%~%"
               (format-goal-key *current-goal-key*)
               *gs-unknown-size*
               *gs-size*
               (format-goal-key (car *current-goal-key*))
               (aref parent-data 2)
               (aref parent-data 1)))))
  (cond ((and (not *sat-case-found?*) (or (and *gs* (= *gs-unknown-size* 0)) *goal-refuted?*))
	 (fmt 0 " Decision: unsat.~%~%"))
	(*sat-case-found?* 
	 (fmt 0 " Decision: sat.~%~%~A~%" (format-model *sat-model*)))
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

      (let ((refuted? (all-cases-refuted)))
	
	(progn
	  (when (or refuted? *sat-case-found?*)
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
		  (when (not (member (car known-child-status)
				     '(:SAT :UNSAT)))
		  
		    ;;
		    ;; At this point, the child has been decided, so the parent's
		    ;;  case who spawned it needs to be updated to reflect this.
		    ;; * We also need to adjust the total number of unknown cases
		    ;;   remaining for the parent.
		    ;;

		    (setf (aref parent-gs child-gs-idx 2)
			  (if refuted?
			      `(:UNSAT :DISCHARGED-BY-SUBGOAL ,*current-goal-key*
				       ,(append (cdr known-child-status)))
			    `(:SAT :SATISFYING-SUBGOAL ,*current-goal-key*
				   ,(append (cdr known-child-status)))))
		    
		    (multiple-value-bind
			(parent-gs-data p-gs-exists?)
			(gethash parent-key *goal-stack-data*)
		      (declare (ignore p-gs-exists?))
		      (setf (aref parent-gs-data 2) 
			    (1- (aref parent-gs-data 2))))
		    
		    (if refuted? 
			(fmt 1 "Trickled refutation up to Case ~A of Goal ~A.~%~%"
			     child-gs-idx parent-key)
		      (fmt 1 "Trickled satisfaction up to Goal ~A.~%~%"
			   parent-key)))))))
	    
	(swap-to-goal (car *current-goal-key*))))

    (fmt 0 "You are already at the root goal.~%~%"))
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
;;; CHECK: Command-line ``unsat,'' ``sat,'' or ``unknown'' function.
;;;

(defun check (f &key verbosity print-model strategy
		non-recursive?)
  (cond 
   ((top-level-syntax-check f)
    (let ((*rahd-verbosity* 
	   (if (rationalp verbosity) verbosity 1)))
      (when *current-goal-key* (r))
      (g f)
      (build-gs :do-not-split-ineqs? t)
      (run-strategy strategy
		    :subgoal-strat
		    (when (not non-recursive?) strategy))
      (let ((refuted? (all-cases-refuted)))
	(fmt 1 "~%[Decision]")
	(fmt 0 "~%")
	(cond (refuted? " unsat~%")
	      (*sat-case-found?* 
	       (format nil " sat~A~%"
		       (if (and print-model *sat-model*)
			   (format nil "~%~A~%" 
				   (format-model *sat-model*))
			 "")))
	      (t  " unknown~%")))))
   (t "")))

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
	((equal (car opts) f)
	 (cond ((not arg?) (values t nil))
	       (t (if (consp (cdr opts))
		      (values t (cadr opts))
		      (values nil f)))))
	(t (cl-find-option f (cdr opts) arg?))))

;;;
;;; GET-FORMULA: Given a string variable list and a string
;;;  formula, parse the formula and get a RAHD S-expr in
;;;  prover representation.
;;;
;;;  * We now restrict ourselves to conjunctions.
;;;

(defun get-formula (&key vars-str formula-str)
  (with-simple-restart 
   (continue-with-new-cmd
    "Continue and enter a new RAHD command.")
   (mapcar #'list (atom-lst (p-formula-str 
			     formula-str 
			     :vars-lst (p-vars-lst vars-str))))))

;;;
;;; RAHD-CL-CHECK: Command-line version of CHECK that accepts
;;;  an S-expression RAHD formula.
;;;

(defun rahd-cl-check ()
  (in-package rahd)
  (handler-bind 
   ((yacc:yacc-parse-error 
     #'(lambda (c)
         (let ((restart (find-restart 'continue-with-new-cmd)))
           (when restart
             (fmt 0 "Parser error: ~A.~%~%" c)
             (invoke-restart restart)))))
    (lex-error 
     #'(lambda (c)
         (let ((restart (find-restart 'continue-with-new-cmd)))
           (when restart
             (fmt 0 "Lexer error: ~A.~%Have you declared all variables?
 Example: 
  rahd-v0.6 -v \"a b c x\" -f \"a*x^2 + b*x + c = 0 /\\ b^2 - 4*a*c < 0\"~%~%" c)
             (invoke-restart restart))))))
   (let ((opts #+ccl ccl:*command-line-argument-list* 
	       #+sbcl sb-ext:*posix-argv*))
     (multiple-value-bind (vars-given? vars-str)
	 (cl-find-option "-v" opts t)
       (multiple-value-bind (formula-given? formula-str)
	   (cl-find-option "-f" opts t)
	 (multiple-value-bind (verbosity-given? verbosity-str)
	     (cl-find-option "-verbosity" opts t)
	   (let ((verbosity (if verbosity-given? 
				(let ((rat-v (car (p-rational verbosity-str))))
				  (if rat-v rat-v 1))
			      1)))
	     (let ((print-model? (cl-find-option "-print-model" opts nil))
		   (div-nz-denoms? (cl-find-option "-div-nz-denoms" opts nil))
		   (interactive? (cl-find-option "-i" opts nil))
		   (ip-evaluator? (cl-find-option "-ip" opts nil))
		   (regression? (cl-find-option "-regression" opts nil))
		   (non-recursive? (cl-find-option "-non-recursive" opts nil)))
	       (when (and (not ip-evaluator?)
			  (or (not formula-given?)
			      (not vars-given?)
			      (>= verbosity 1)))
		 (progn
		   (fmt 0 "
RAHD: Real Algebra in High Dimensions ~A
 designed and programmed by grant o. passmore {g.o.passmore@sms.ed.ac.uk}
  with intellectual contributions from p.b.jackson, b.boyer, g.collins, 
  h.hong, f.kirchner, j moore, l.de moura, s.owre, n.shankar, a.tiwari,
  v.weispfenning and many others.  This version of RAHD is using Maxima 
  multivariate factorisation & SARAG subresultant PRS + Bernstein bases.~%~%" 
			*rahd-version*)
		   (when (and (or (not formula-given?) 
				  (not vars-given?))
			      (not interactive?)
			      (not ip-evaluator?))
		     (fmt 0 
			  " Error: Variables and formula not given.

 Usage: ~A -v \"vars list\" -f \"formula\" <options>
   or   ~A [-i | -ip | -strategies | -strategy # | -regression]

  with options:

    -verbosity q      (0<=q<=10)     degree of proof search output (def: 1)
    -strategy #                      execute an explicitly given proof strategy
    -print-model                     print a counter-model, if found
    -print-proof                     print a proof trace, even on failure
    -print-fail                      if a decision is not reached, print 
                                      a failure report (unrefuted cases)
    -regression                      test build against regression suite
    -run s                           use defined proof strategy named s
                                      (equivalent to `-strategy [run s]')
    -strategies                      list all defined proof strategies
    -i                               interactive top-level
    -ip                              machine-oriented batch evaluator

  where n is a natural, q is a rational presented as `a/b' or `a' for integers a,b,
        $ is either `on', `off' or `only' (def: `on'), 
        % is either `sturm' or `bernstein' (def: `sturm'),
        s is a name of a defined proof strategy (def: `waterfall'),
        # is an explicitly given proof strategy.~%"
			
			(car opts)
			(car opts)))))
	     (cond (regression? (wrv (if (rationalp verbosity) verbosity 1) 
				     (rahd-regression-suite)))
		   (interactive? (r-repl))
		   (ip-evaluator? (p-repl))
		   (formula-given?
		    (when div-nz-denoms?
		      (setq *div-nz-denoms* t))
		    (fmt 0 (check (get-formula :formula-str formula-str
					       :vars-str vars-str)
				  :verbosity (when (rationalp verbosity)
					       (min verbosity 10))
				  :print-model print-model?
				  :strategy '(run waterfall)
				  :non-recursive? non-recursive?))))
	     (fmt 0 "~%")))))))))
  
;;;
;;; Print all goals.
;;;

(defun print-all-goals ()
  (cond (*goal-stack-keys*
	 (fmt 0 "~%All goals: ~%")
	 (dolist (g *goal-stack-keys*)
	   (fmt 0 " ~A~%" (format-goal-key g)))
	 (fmt 0 "~%"))
	(t (fmt 0 " ~%No goals.~%~%"))))