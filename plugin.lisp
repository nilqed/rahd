;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Plugins mechanism.
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
;;; This file: began on         23-February-2011,
;;;            last updated on  24-February-2011.
;;;

;;;
;;; Require SBCL posix lib so plugins can be aware of their processes.
;;;

(require :sb-posix)

;;;
;;; Plugins path.  Eventually, will make this updatable from ~/.rahdrc .
;;;

(defparameter *plugins-path*
  "./plugins/")

;;;
;;; Register list of plugin files here.
;;;

(defparameter *plugin-files*
  '("qepcad.lisp"
    "redlog.lisp"))

;;;
;;; Install a plugin.
;;;

(defun install-plugin (&key cmf-str cmf-fcn cmf-args)
  (install-cmf :cmf-str cmf-str
	       :cmf-fcn cmf-fcn
	       :cmf-args cmf-args)
  (build-cmf-sym-hash)
  (fmt 0 "  cmf ~A has been installed.~%~%" cmf-str))

;;;
;;; Prepend Plugins Path to a file string.
;;;

(defun prepend-plugins-path (f)
  (concatenate 'string *plugins-path* f))

;;;
;;; Refresh plugins.
;;;

(defun refresh-plugin (f)
  (declaim #+sbcl(sb-ext:muffle-conditions style-warning))
  (fmt 0 "~%Loading plugin ~A:~%" f)
  (load (prepend-plugins-path f))
  (declaim #+sbcl(sb-ext:unmuffle-conditions style-warning)))

(defun refresh-plugins ()
  (dolist (f *plugin-files*)
    (refresh-plugin f)))

(refresh-plugins)