;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; ** RAHD<->Maxima interface **
;;;      exports: multivariate factorisation (factor p),
;;;               signed subresultant prs (subres p q v),
;;;               multivariate discriminant (discriminant p v),
;;;               multivariate resultant (resultant p q v),
;;;               multivariate square-free base (sqr-free-dp p)
;;;                                         and (sqr-free-dps ps).
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         28-May-2010,
;;;            last updated on  21-August-2010.
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

;;;
;;; Given two RAHD polynomials in prover representation and a variable
;;;  s.t. deg(p) > deg(q), use Maxima and SARAG to obtain signed 
;;;  subresultant polynomial remainder sequence.
;;;
;;; We return two lists:
;;;   (values SSUBRES-PRS SSUBRES-PRS-COEFFS).
;;;
;;; The latter is what we use as part of our projection operator for
;;;  cylindrical algebraic decomposition.
;;;

(defun ssubres (p q var)
  (let ((raw-maxima-lsts
	 (maxima::$eval_string
	  (format nil "sSubRes(~A,~A,~A)"
		  (rahd-p-to-maxima (term-to-bin-ops p))
		  (rahd-p-to-maxima (term-to-bin-ops q))
		  (rahd-p-to-maxima var)))))
    (let ((maxima-ssprs-lst (cdadr raw-maxima-lsts))
	  (maxima-ssprs-coeff-lst (cdaddr raw-maxima-lsts)))
      (let ((ssprs-lst (mapcar #'maxima-p-to-rahd maxima-ssprs-lst))
	    (ssprs-coeff-lst (mapcar #'maxima-p-to-rahd maxima-ssprs-coeff-lst)))
	(values ssprs-lst ssprs-coeff-lst)))))

;;;
;;; Given a RAHD polynomial in prover representation and a variable,
;;;  return the discriminant of the polynomial w.r.t. the variable.
;;;
;;; For whatever reason, I found that sometimes Maxima's discriminant
;;;  command returns weirdly unsimplified products of rational functions.
;;;  Example: 
;;;
;;;   (MAXIMA::$EVAL_STRING
;;;      "discriminant((-1*(X*(C*C))) + (-1*(S*(C*C))) + (X*X),C)")
;;;
;;;    returns 
;;;
;;;   (+ (* -4 (* (EXPT S 2) (* (EXPT (+ (* -1 S) (* -1 X)) -1) (EXPT X 2))))
;;;    (+ (* -8 (* S (* (EXPT (+ (* -1 S) (* -1 X)) -1) (EXPT X 3))))
;;;      (* -4 (* (EXPT (+ (* -1 S) (* -1 X)) -1) (EXPT X 4))))).
;;;
;;;  Note that many of the EXPT's have a power of -1.
;;;  
;;;  But, it seems that if we apply Maxima's factor command to the result, 
;;;   it then pushes through the simplification. Very weird. I need to write
;;;   the Maxima mailing list and figure this out for good.
;;;
;;;  Example with applying factor(discriminant(...)):
;;;    (* 4 (* (EXPT X 2) (+ S X))) as expected.
;;;  It also works with ratsimp, ratexpand.
;;;  Ratsimp seems to be faster than factor.
;;;

(defun discriminant (p var)
  (when (member var (gather-vars p))
    (maxima-p-to-rahd 
     (maxima::$eval_string
      (format nil "ratsimp(discriminant(~A,~A))"
	      (rahd-p-to-maxima (term-to-bin-ops p))
	      (rahd-p-to-maxima var))))))

;;;
;;; Given a RAHD polynomial P in prover representation, return a
;;;  list of RAHD polynomials corresponding to a square-free
;;;  decomposition of P.
;;;
;;; We also have a version for lists of polynomials: This is
;;;  SQR-FREE-DPS (PS) below.
;;;
;;; List is in prover notation.
;;;

(defun sqr-free-dps (ps &key factor?)
  (let ((sqr-free-base nil))
    (dolist (p ps)
      (let ((p-result (sqr-free-dp p :factor? factor?)))
	(setq sqr-free-base
	      (union sqr-free-base 
		     p-result
		     :test 'equal))))
    sqr-free-base))

(defun sqr-free-dp (p &key factor?)
  (let* ((mp (rahd-p-to-maxima (term-to-bin-ops p)))
	 (sfm (maxima::$eval_string 
	       (format 
		nil 
		(if factor? "factor(~A)" "sqfr(~A)") 
		mp)))
	 (sfr (maxima-p-to-rahd sfm)))
    (if (and (consp sfr) (member (car sfr) '(* EXPT)))
	(extract-p-bases sfr)
      (list sfr))))

(defun extract-p-bases (p)
  (cond ((rationalp p) nil)
	((varp p) (list p))
	((consp p)
	 (case (car p)
	   (EXPT (list (cadr p)))
	   (* (let ((l1 (extract-p-bases (cadr p)))
		    (l2 (extract-p-bases (caddr p))))
		(cond ((and l1 l2)
		       (union l1 l2 :test 'equal))
		      (l1 l1)
		      (l2 l2))))
	   (otherwise (list p))))))

;;;
;;; Given a pair of polynomials and a var, return the resultant
;;;  of the two polynomials w.r.t. var.
;;;
;;; Polynomials are given in prover notation.
;;;

(defun resultant (p q var)
  (maxima-p-to-rahd
   (maxima::$eval_string 
    (format nil "resultant(~A,~A,~A)"
	    (rahd-p-to-maxima (term-to-bin-ops p))
	    (rahd-p-to-maxima (term-to-bin-ops q))
	    (rahd-p-to-maxima var)))))
			 
;;;
;;; ***************************************************************
;;;  RAHD<->Maxima translation 
;;; ***************************************************************
;;;

;;;
;;; Convert Maxima polynomial to RAHD (prover notation) polynomial
;;;  extended with the EXPT operator.
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
	       ((maxima::mplus maxima::mtimes maxima::rat)
		(let ((rahd-op (case op
				 (maxima::mplus '+)
				 (maxima::mtimes '*)
				 (maxima::rat '/))))
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