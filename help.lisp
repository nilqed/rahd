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
;;;            last updated on  17-February-2011.
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
    ("check" .
     "Usage: check~%
 Checks the satisfiability of the current context
  using the default proof strategy.

 * See assert for more on asserting formulas.
 * See default-strategy for setting the default strategy.
 * See show for viewing the current context.
 * See reset for clearing the current context.~%~%")
    ("cmfs" .
     "Usage: cmfs~%
 List available CMFs.

 * See apply for more on executing CMFs.
 * See run for more on executing proof strategies.~%~%")
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

 * See build-goalset for building a goalset from a goal.
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
 * See build-goalset for building a goalset from a goal.
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
   apply assert build-gs check cg cmfs default-strategy defrule defruleset 
   defstrat e goal goalkeys goalset help lisp options opens proj-order quit 
   reset rules rulesets set set? show status strats up unset vars verbosity 
   watch unwatch. ~%~%")))))