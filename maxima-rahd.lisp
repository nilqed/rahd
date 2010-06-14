;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; ** RAHD<->Maxima interface **
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         28-May-2010,
;;;            last updated on  30-May-2010.
;;;

(in-package rahd)

(defparameter *maxima-src-path* 
  (parse-namestring 
   (format 
    nil 
    "~A/~A" *default-pathname-defaults* "maxima-5.20.1/src/")))

(defparameter *prev-pathname-defaults* *default-pathname-defaults*)

;;;
;;; Initialise Maxima build living under RAHD source tree.
;;;

(defun init-maxima ()
  (setq *default-pathname-defaults* *maxima-src-path*)
  (load "maxima-build")
  (maxima-load)
  (in-package maxima)
  (maxima::initialize-real-and-run-time)
  (intl::setlocale)
  (maxima::set-locale-subdir)
  (maxima::adjust-character-encoding)
  (maxima::set-pathnames)
  (when (boundp '*maxima-prefix*)
    (push (pathname (concatenate 'string *maxima-prefix* "/share/locale/"))
	  intl::*locale-directories*))
  (maxima::load "../share/contrib/stringproc/eval_string.lisp")
  (maxima::$load "../share/contrib/sarag/sarag.mac")
  (in-package rahd)
  (setq *default-pathname-defaults* *prev-pathname-defaults*))

;;;
;;; Build Maxima living under RAHD source tree.
;;;

(defun build-maxima ()
  t)

;;;
;;; Example: * (maxima::$eval_string "factor(4*x^2*a^2 + 4*x*a*b + b^2)")
;;;
;;; ((MAXIMA::MEXPT MAXIMA::SIMP MAXIMA::FACTORED)
;;;  ((MAXIMA::MPLUS MAXIMA::SIMP MAXIMA::IRREDUCIBLE) MAXIMA::$B
;;;   ((MAXIMA::MTIMES MAXIMA::SIMP MAXIMA::RATSIMP) 2 MAXIMA::$A MAXIMA::$X))
;;;

;;;
;;; Convert Maxima polynomial to RAHD (prover notation) polynomial.
;;;

;; (defun maxima-p-to-rahd (m)
;;   (cond ((endp m) nil)
;; 	(