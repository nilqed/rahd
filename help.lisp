;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Help system for the interactive top-level.
;;;
;;; Written by Grant Olney Passmore
;;; * Postdoc, Cambridge-Edinburgh EPSRC grant
;;;    ``Automatic Proof Procedures for Polynomials and Special Functions.''
;;;   Postdoctoral Associate, Clare Hall, University of Cambridge
;;;   Research Associate, LFCS, University of Edinburgh
;;;
;;; The following institutions have provided support for RAHD development
;;;  through funding the following positions for me (Passmore):
;;;   - Ph.D. Student, University of Edinburgh,
;;;   - Visiting Fellow, SRI International,
;;;   - Research Intern, Microsoft Research,
;;;   - Visiting Researcher, INRIA/IRISA.
;;;
;;; These positions have been crucial to RAHD progress and we thank the host 
;;;  institutions and groups very much for their support and encouragement.
;;;
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/.
;;; 
;;; This file: began on         12-December-2010,
;;;            last updated on  02-March-2011.
;;;

(defparameter *help-alist*
  '(("apply" .
     "Usage: apply <cmf-name>~%
 Applies CMF cmf-name to the open cases of the current goal.
 Example:
  apply simp-zrhs

 * See cmfs for available CMFs.
 * See run for how to execute proof strategies.
 * See watch for how to monitor progress of CMFs upon cases.~%~%")
    ("assert" .
     "Usage: assert <formula>~%
 Asserts a formula as an assumption in the current context.~%
 Note that an asserted formula must be either a single literal 
  or a conjunction of literals.
 Also, all variables in the formula must be declared.

 Example:
  assert x^2 + (x - z)^2 > 0 /\\ z >= 5

 * See vars for more on variable declaration.
 * See check for checking the satisfiability of a context.
 * See show for viewing the current context.
 * See reset for clearing the current context.~%~%")
    ("build-gs" .
     "Usage: build-gs~%
Build a goalset from the current collection of assertions.
This promotion from a collection of assertions to a goalset
 is required before proof strategies may be applied.

 * See assert for more on asserting formulas.
 * See default-strategy for setting the default strategy.
 * See e for executing an explicit proof strategy.
 * See show for viewing the current context.
 * See reset for clearing the current context.~%~%")
    ("check" .
     "Usage: check       -or-        check 1.~%
 Checks the satisfiability of the current context
  using the default proof strategy.

 When a simple \"check\" is issued, the current assertion
  context is promoted to a goalset and the default strategy
  is used to analyse it.  If any subgoals are generated,
  then the default strategy is applied to them recursively.

 When \"check 1\" is issued, the process is the same except
  for the following: If subgoals are generated, they will
  be left alone, i.e., no strategy will be automatically
  applied to them.

 To be precise, \"check\" is effectively the same as

   > build-gs
   > e <default-strategy>,

 while \"check 1\" is effectively the same as

   > build-gs
   > e1 <default-strategy>.

 * See assert for more on asserting formulas.
 * See default-strategy for setting the default strategy.
 * See show for viewing the current context.
 * See reset for clearing the current context.~%~%")
    ("cmfs" .
     "Usage: cmfs~%
 List available CMFs.

 * See apply for more on executing CMFs.
 * See run for more on executing proof strategies.~%~%")
    ("e" .
     "Usage: e <explicit-proof-strategy>~%
 Executes explicit-proof-strategy against the current goalset,
  with recursive subgoaling.

 Example: e [demod-lin; run stable-simp; run waterfall]

 Note that if any subgoals are generated during the run of
  explicit-proof-strategy, then explicit-proof-strategy
  will be run against them recursively.

 For a non-recursive method of running strategies, see e1.

 * See e1 for more on running strategies non-recursively.
 * See assert for more on asserting formulas.
 * See build-gs for building a goalset from context.
 * See cg for changing between active goals.
 * See default-strategy for setting the default strategy.
 * See opens for viewing open cases.
 * See watch for how to monitor progress of CMFs upon cases.~%~%")
    ("e1" .
     "Usage: e1 <explicit-proof-strategy>~%
 Executes explicit-proof-strategy against the current goalset,
  with non-recursive subgoaling.

 Example: e1 [demod-lin; run stable-simp; run waterfall]

 Note that if any subgoals are generated during the run of
  explicit-proof-strategy, then they will be left alone, i.e.,
  explicit-proof-strategy will not be run against them.

 For a recursive method of running strategies, see e.

 * See e for more on running strategies recursively.
 * See assert for more on asserting formulas.
 * See build-gs for building a goalset from context.
 * See cg for changing between active goals.
 * See default-strategy for setting the default strategy.
 * See opens for viewing open cases.
 * See watch for how to monitor progress of CMFs upon cases.~%~%")
    ("goals" .
     "Usage: goals~%
 List all known (sub)goals.

 * See cg for changing between active goals.
 * See up for navigating up to a goal's parent.
 * See build-gs for building a goalset.
 * See status for viewing the decision status of a goal.
 * See opens for viewing the open cases of a goal.~%~%")
    ("help" .
     "Usage: help <keyword>~%
 Invoke 'help' with no arguments for possible keywords.~%~%")
    ("quit" .
     "Usage: quit~%
 Quit the RAHD toplevel and completely exit the program.~%~%")
    ("lisp" .
     "Usage: lisp <lisp-form>~%
 Execute a raw Lisp form.
 Of course, one can use this to redefine system data and
  render the system unsound.  Nevertheless, it is available
  for power users.  Be warned: If your proof script utilises
  a raw Lisp execution, nothing can be guaranteed about the
  soundness of the alleged `proof' found by the system.

 There is no undo mechanism: If you redefine system data
  and wish to return to a fresh RAHD session, you must
  quit the session and start over.

  Example:
   lisp (expt 2 10)

 * See quit for leaving the RAHD session.~%~%")
    ("status" .
     "Usage: status~%
 Show judgment status of current proof context.
 Also, will display a model if one has been computed.

 * See check for checking the satisfiability of a context.
 * See set for more on setting prover options.
 * See options for more on possible prover options.~%~%")
    ("strategies" .
     "Usage: strategies~%
 List all defined proof strategies.

 * See strategy for how to view the parsed definition of
    a proof strategy.~%~%")
    ("strategy" .
     "Usage: strategy <strategy-name>~%
 Print the parsed definition of a proof strategy.

 * See strategies for how to list all defined strategies.~%~%")
    ("up" .
     "Usage: up~%
 Navigate to the current goal's parent, if it exists.

 In the process, any decision reached as to the satisfiability
  of the current goal will be percolated appropriately to the
  parent.

 In particular, if the current goal is a subgoal and has been
  found unsatisfiable, the parent's case which generated the
  subgoal will be closed.  If instead the current goal is a
  subgoal which has been found satisfiable, this implies the
  satisfiability of the entire parent goal, and this judgment
  will be inherited by the parent.

 * See cg for changing between active goals.
 * See goals for listing all goals.
 * See build-gs for building goalsets.
 * See opens for viewing the open cases of a goal.~%~%")
    ("vars" .
     "Usage: vars <variables-list>~%
 Declares variables for use in the current context.~%
 Note that variable names are case insensitive.

 Example:
  vars x1 x2 x3

 If no variables-list is given, then the current list
  of declared variables will be displayed.

 * See assert for more on asserting formulas.~%~%")
    ("verbosity" . 
     "Usage: verbosity <verbosity-level>~%
 Set current prover verbosity level to a rational
  number in the range [0..10].
 The default level is 0.  The higher the level, the
  more information is displayed during proof search.

 Roughly, some key levels are as follows:

   0: only final judgment information displayed,
   1: names of CMFs applied displayed as they are
       used by proof strategies,
   2: names and basic progress information of CMFs
       displayed as they are used by proof strategies,
   3: beginning debugging information displayed,
   .
   .
  10: full debugging information displayed.

 * See check for more on checking the current context.~%~%")
    ("watch" .
     "Usage: watch <case-number>~%
Watch a case in the current goalset.
This causes the watched case to be printed before every
 RAHD command prompt.  This is useful if one is working
 on a particular case and wishes to observe the changes
 made to the case by CMF and proof strategy execution.

 Example:
  watch 0

 * See build-gs for building a goalset from a goal.
 * See apply for CMF execution.
 * See run for proof strategy execution.
 * See goalset for viewing the current goalset.
 * See status for viewing the current context judgment.~%~%")
  ("unwatch" .
   "Usage: unwatch <case-number>~%
Stop watching a case in the current goalset.

 Example:
  unwatch 0

 * See watch for case watching.
 * See build-gs for building a goalset from a goal.
 * See apply for CMF execution.
 * See run for proof strategy execution.
 * See goalset for viewing the current goalset.
 * See status for viewing the current context judgment.~%~%")
    ))

(defun toplevel-help (arg)
  (let* ((help-assoc (assoc arg *help-alist* :test 'equal))
         (assoc-str (if help-assoc (cdr help-assoc) nil)))
  (cond (assoc-str (fmt 0 assoc-str))
        (t  (fmt 0 "Help with RAHD toplevel.  Try 'help <keyword>' ~
  where keywords are:~%
   assert build-gs check cg cmfs default-strategy defrule defruleset 
   defstrat e e1 goal goals goalset help lisp options opens proj-order 
   quit reset rules rulesets set set? show status strategies up unset 
   unwatch vars verbosity watch. ~%~%")))))