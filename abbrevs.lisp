;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; ** Some short abbreviations for RAHD interface commands and tactics **
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         28-Feb-2009,
;;;            last updated on  01-July-2010.
;;;

;;;
;;; Some abbreviations for RAHD commands.
;;;

(defun r () (rahd-reset-state))

(defun b () (build-gs))

(defun p (&key bound case) 
  (pug :bound bound :case case))

(defun tr () (tactic-replay))

(defun rtr () (setq *tactic-replay* nil))

(defun epa () (setq *enable-proof-analysis* t))
(defun ppa () (print-proof-analysis))
(defun pa () (print-proof-analysis))

(defun go!pa () (epa) (go!) (ppa))

(defmacro wrv (&rest rst)
  `(with-rahd-verbosity ,@rst))

(defmacro wrs (&rest rst)
  `(with-rahd-verbosity 0 ,@rst))

(defmacro wrd (&rest rst)
  `(with-rahd-debugging ,@rst))

;; ``with outcome only''

(defmacro woo (&rest rst)
  `(with-rahd-verbosity 1/2 ,@rst))

(defparameter *regression-suite* nil)

(defmacro rrs (&rest rst)
  `(rahd-regression-suite ,@rst))

(defun gr (n)
  (r)
  (g (car (nth n *regression-suite*)))
  (fmt 0 " Regression suite entry ~A installed as the active goal.~%" n)
  t)

(defun ctr ()
  (setq *tactic-replay* nil))

(defun srv (n)
  (setq *rahd-verbosity*  n)
  (fmt 0 "~% RAHD verbosity set to ~A.~%~%" n)
  t)

(defun u ()
  (up))

(defun swap-to-subgoal (k)
  (swap-to-goal k))

(defun cd (k)
  (swap-to-goal k))

(defparameter *rrs*
  *regression-suite*)

(defparameter *rs*
  *regression-suite*)

(defun c ()
  (current-stats))

(defun cg ()
  (current-stats :show-goal t))

;;;
;;; Some abbreviations for RAHD tactics.
;;;

(defun ocad () (open-ex-inf-cad))

(defun ofcad () (open-frag-ex-inf-cad))

(defun gcad () (gen-ex-cad))

(defun ss () (stable-simp))

(defun sz () (simp-zrhs))

(defun srn () (simp-real-null))

;;;
;;; Some control macros.
;;;

;;;
;;; EXEC-UNTIL-SAT: Execute a sequence of forms (usually tactics)
;;;  but cease execution if a SAT case has been found.
;;;

(defmacro exec-until-sat (&rest rst)
  (let ((out nil))
    (dolist (r rst)
      (setq out (cons `(when (not *sat-case-found?*) ,r) out)))
    `(progn ,@(reverse out))))

