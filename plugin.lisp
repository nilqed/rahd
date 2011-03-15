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
;;;            last updated on  15-March-2011.
;;;

;;;
;;; Require SBCL posix lib so plugins can be aware of their processes.
;;;

(require :sb-posix)

;;;
;;; Get user's home directory.
;;;

(defun home-dir ()
  (sb-unix::posix-getenv "HOME"))

;;;
;;; Plugins path.  Eventually, will make this updatable from ~/.rahdrc .
;;;

(defun plugins-path ()
  (concatenate 'string (home-dir) "/.rahd/plugins/"))

;;;
;;; Register list of plugin source Lisp files here.
;;;

(defparameter *plugin-files*
  '("qepcad.lisp"
    "redlog.lisp"))

;;;
;;; Prepend Plugins Path to a file string.
;;;

(defun prepend-plugins-path (f)
  (concatenate 'string (plugins-path) f))

;;;
;;; Check to see if plugins path and associated files exist.
;;;

(defun plugins-path-ok? ()
  (and (probe-file (plugins-path))
       (let ((out t))
	 (dolist (f *plugin-files*)
	   (setq out 
		 (and (probe-file
		       (prepend-plugins-path f))
		      out)))
	 out)))
	 
;;;
;;; Run plugin cmf tests.
;;;

(defun plugin-cmf-tests (&key cmf-fcn cmf-tests)
  (fmt 0 "~% Performing plugin cmf tests (~A). ~%" (length cmf-tests))
  (let ((passed? t) (i 0))
    (dolist (test cmf-tests)
      (setq i (1+ i))
      (let ((p? (equal (apply cmf-fcn (list (car test))) (cdr test))))
	(cond 
	 (p? (fmt 0 "  test ~A passed.~%" i))
	 (t (fmt 0 "  test ~A failed.~%" i)
	    (setq passed? nil)))))
    (when passed?
      (fmt 0 " All tests passed.~%~%"))
    passed?))

;;;
;;; A simple no-op CMF.
;;; Note: Additional arguments need to be added here as plugins
;;;  are defined which take optional arguments.
;;;

(defun noop-cmf (x &key open?)
  x)

;;;
;;; Install a plugin.
;;;
;;; CMF-Tests is a list of pairs of the form:
;;;  ((rahd-case . correct-response-from-cmf) ...).
;;; A plugin CMF must pass all of its tests before it is
;;;  made active and available to strategies.
;;;

(defun install-plugin (&key cmf-str cmf-fcn cmf-args cmf-tests)
  (let ((passed-tests? (plugin-cmf-tests 
			:cmf-fcn cmf-fcn
			:cmf-tests cmf-tests)))
    (cond (passed-tests?
	   (install-cmf :cmf-str cmf-str
			:cmf-fcn cmf-fcn
			:cmf-args cmf-args)
	   (build-cmf-sym-hash)
	   (fmt 0 "  .:. cmf ~A has been installed.~%~%" cmf-str))
	  (t (fmt 0 "
 Unfortunately, cmf ~A did not pass its tests.~%
 This probably means that you have not configured 
  your environment correctly so that the RAHD plugin
  can interact with the associated external tool.~%
 Since the tests weren't passed, RAHD cannot let
  you use this cmf in any proof strategies.~%
 But, we will still introduce the symbol for you
  (~A) and simply associate it with 
  the identity (i.e., no-op) cmf.~%
 If you later fix your environment and want to
  try again, you can type 'refresh-plugins' at 
  the RAHD top-level.~%~%"
		  cmf-str cmf-str)
             (install-cmf :cmf-str cmf-str
                          :cmf-fcn #'noop-cmf
                          :cmf-args cmf-args)
             (build-cmf-sym-hash)))))

;;;
;;; Refresh plugins.
;;;

(defun refresh-plugin (f)
  (declaim #+sbcl(sb-ext:muffle-conditions style-warning))
  (fmt 0 "~%Loading plugin ~A:~%" f)
  (load (prepend-plugins-path f))
  (declaim #+sbcl(sb-ext:unmuffle-conditions style-warning)))

(defun refresh-plugins ()
  (if (plugins-path-ok?)
      (dolist (f *plugin-files*)
	(refresh-plugin f))
    (fmt 0 " 
Error: There is a problem with the following path
 which is required for this build of RAHD:~%
  Path: ~A.~%~%
 Please make sure it exists and contains the 
  required files.~%~%" (plugins-path))))

(refresh-plugins)