;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; ** RAHD<->Maxima interface **
;;;      exports: multivariate factorisation (factor p),
;;;               signed subresultant prs (subres p q).
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         28-May-2010,
;;;            last updated on  27-June-2010.
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

;;; ***************************************************************
;;;  Imported Maxima Functions
;;; ***************************************************************

;;;
;;; Given a RAHD polynomial in prover representation, use Maxima
;;;  to factor it.
;;;
;;; Note: Soon (writing on 27-June-2010) we'll want to cache factor-
;;;   isations.
;;;

(defun factor (p)
  (maxima-p-to-rahd
   (maxima::$eval_string 
    (format nil "factor(~A)" 
	    (rahd-p-to-maxima (term-to-bin-ops p))))))





;;; ***************************************************************
;;;  RAHD<->Maxima translation 
;;; ***************************************************************

;;;
;;; Convert Maxima polynomial to RAHD (prover notation) polynomial.
;;;

(defun maxima-p-to-rahd (m)
  (cond 
   ((symbolp m) (intern (subseq (format nil "~:@(~a~)" m) 1)))
   ((numberp m) m)
   ((endp m) m)
	(t (let ((op (caar m)))
	     (case op
	       (maxima::mexpt 
		`(expt ,(maxima-p-to-rahd (cadr m))
		       ,(maxima-p-to-rahd (caddr m))))
	       ((maxima::mplus maxima::mtimes)
		(let ((rahd-op (case op
				 (maxima::mplus '+)
				 (maxima::mtimes '*))))
		  (cond ((= (length m) 3)
			 `(,rahd-op ,(maxima-p-to-rahd (cadr m))
				    ,(maxima-p-to-rahd (caddr m))))
			((> (length m) 3)
			 `(,rahd-op ,(maxima-p-to-rahd (cadr m))
				    ,(maxima-p-to-rahd `((,op) ,@(cddr m)))))))))))))
		  

;;;
;;; Convert RAHD prover rep polynomial into Maxima human-notation polynomial.
;;;

(defun rahd-p-to-maxima (term)
  (cond ((equal term nil) "")
	((numberp term) 
	 (if (< term 0) 
	     (format nil "(0 - ~A)" (write-to-string (- (rational term))))
	   (write-to-string (rational term))))
	((varp term) (format nil "~A" term))
	((consp term)
	 (let ((cur-f (car term))
	       (cur-x (cadr term))
	       (cur-y (caddr term)))
	   (concatenate 
	    'string
	    "(" (rahd-p-to-maxima cur-x)
	    (if (equal cur-f '*) "*" 
	      (format nil " ~A " (write-to-string cur-f)))
	    (rahd-p-to-maxima cur-y) ")")))))