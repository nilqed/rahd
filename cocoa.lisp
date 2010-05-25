;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A decision method for the existential theory of real closed fields.
;;;
;;; * Fast GB interface to the CoCoA Commutative Algebra System *
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         25-Sept-2008,
;;;            last updated on  14-Nov-2008.
;;;

(in-package RAHD)

;;;
;;; COCOA-VARS-MAP: A global snapshot of the last used variable mapping connecting the
;;;  polynomial ring we construct within CoCoA and our internal ring governed by MO<.
;;;  ** This is only used if RAHD-DEBUG is enabled.

(defparameter *cocoa-vars-map* nil)

;;;
;;; EXEC-COCOA-GB-FOR-CASE: Given a case, extract its equations, convert them in ZRHS form,
;;; construct a GB query for CoCoA, execute it, parse its output, check to make sure the
;;; resulting GB reduces the original equations to zero, and then return it in RAHD ALG-REP. 
;;; If any of this fails, we return NIL.
;;;

#+ccl (defun exec-cocoa-gb-for-case (c) (declare (ignore c)) nil)

#+allegro
(defun exec-cocoa-gb-for-case (c)
  (let ((eqs (gather-eqs c)))
    (if (not eqs) nil

      ;;
      ;; Create the indeterminate mapping from PROVER-VARS (*vars-table*) --> X[i] CoCoA indeterminate format.
      ;; Note: We must build the polynomial ring in CoCoA s.t. our internal MO< term ordering exactly matches
      ;;       CoCoA's internal term ordering.  SORT-VARS-UNDER-ACTIVE-TM-ORD, together with using the
      ;;       DegRevLex ordering matrix in CoCoA, guarantees this will be the case, so long as active-mo< is
      ;;       #<Function DEG-REV-LEX<>.
      ;;
      
      (let ((cocoa-vars-map (cocoa-map-vars-to-v-array (sort-vars-under-active-tm-ord (all-vars-in-conj eqs)))))

	;; Map the equations using COCOA-VARS-MAP s.t. all indeterminates of form X[i]

	(let ((eqs-in-cocoa-format (cocoa-v-subst-from-prover eqs cocoa-vars-map)))

	  ;; Put eqs into string format for CoCoA, now x[i] (lower-case)

	  (let ((eqs-str-in-cocoa-format (mapcar #'string-downcase (cocoa-gb-polys eqs-in-cocoa-format))))
	    (let ((cocoa-gb-str (cocoa-gb-string eqs-str-in-cocoa-format 
						 (cocoa-polynomial-ring (length cocoa-vars-map)))))
	      (with-open-file (cocoa-gb-in (work-pathify "cocoa-gb.in") :direction :output :if-exists :supersede)
			      (format cocoa-gb-in cocoa-gb-str))
	      (#+allegro excl:run-shell-command
			 #+cmu extensions:run-program
			 "./cocoa-gb.bash")
	      (let ((computed-gbasis-lst nil))
		(with-open-file (cocoa-gb-out (work-pathify "cocoa-gb.out") :direction :input)
		   (do ((l (read-line cocoa-gb-out) (read-line cocoa-gb-out nil 'eof)))
		       ((eq l 'eof) "eof")
		       (setq computed-gbasis-lst (cons l computed-gbasis-lst))))

		;; Note, the GBasis str lst is now in reverse order of the CoCoA presentation

		(if *rahd-debug* (setq *cocoa-vars-map* cocoa-vars-map))
		(reverse (mapcar #'(lambda (poly) (cocoa-poly-to-alg-rep poly cocoa-vars-map)) computed-gbasis-lst))))))))))

;;;
;;; COCOA-GB-STRING: Given CoCoA prepared poly strings and a CoCoA prepared polynomial ring
;;; string, return the CoCoA commands to compute the reduced GB of the ideal generated by
;;; the represented polys.
;;;
;;; Idea: Experiment with Radical(...) here, selectively then disabling (RCR-SVARS) from the 
;;;  waterfall (13-Nov-08).
;;;

(defun cocoa-gb-string (c-polys c-ring)
  (format nil 
"Use ~A, DegRevLex;
I := Ideal([~(~{~A~#[~:;, ~]~}~)]);
G := ReducedGBasis(I);
D := OpenOFile(\"~A\");
Foreach X In G Do
 PrintLn X On D;
EndForeach;
Close(D);
" c-ring c-polys (work-pathify "cocoa-gb.out")))

;;;
;;; COCOA-V-SUBST-PROVER-FROM-PROVER: Given eqs and cocoa-vars-map, return 
;;; the result of doing the CoCoA vars-map substitution upon the case's equalities.
;;;

(defun cocoa-v-subst-from-prover (eqs cocoa-vars-map)
  (let ((out-eqs eqs))
    (dotimes (i (length cocoa-vars-map))
      (setq out-eqs (subst (intern (format nil "X[~D]" i)) (aref cocoa-vars-map i) out-eqs)))
    out-eqs))

;;;
;;; SORT-VARS-UNDER-ACTIVE-TM-ORD: Given a list of variabes, sort it w.r.t. the current
;;; variable ordering induced by *VARS-TABLE*.  Note that CoCoA adheres to the same 
;;; convention we do when using DegRevLex as the term ordering: That is, variable x[i]
;;; is higher in the term ordering than x[i+1] is.  So, we can sort the variables here
;;; in the exact relative order as they appear in *VARS-TABLE*.  If we were using
;;; an Xel-based ordering in CoCoA, however, we would have to reverse this ordering
;;; to obtain confluence w.r.t. POLY-MULTIV-/ of the resulting reduced GBasis.
;;;

(defun sort-vars-under-active-tm-ord (vs)
  (let ((f< #'(lambda (x y) 
		(< (find-var x *vars-table* 0)
		   (find-var y *vars-table* 0)))))
    (sort vs f<)))

;;;
;;; COCOA-MAP-VARS-TO-V-ARRAY: Given the variables in a conjunction, associate them to the
;;; cocoa-vars-map and return cocoa-vars-map as an array.
;;;
;;; Note: We must sort the variables in COCOA-VARS-MAP so that they are in the exact same
;;;  relative order as they are in *VARS-TABLE*, else the term ordering used in CoCoA will not
;;;  match the term ordering we use internally for algebraic computations, causing the
;;;  computed reduce GBasis to not induce a confluent rewriting system via POLY-MULTIV-/.
;;;  This is done by SORT-VARS-UNDER-ACTIVE-TM-ORD.
;;;

(defun cocoa-map-vars-to-v-array (vs)
  (let ((l (length vs)))
    (let ((cocoa-vars-map (make-array l)))
      (let ((c 0))
	(dolist (v vs)
	  (setf (aref cocoa-vars-map c) v)
	  (setq c (1+ c))))
      cocoa-vars-map)))

;;;
;;; COCOA-POLYNOMIAL-RING: Given the number of unique indeterminates appearing in the eqs
;;; of a case, return the CoCoA construction for the smallest polynomial ring over Q that will
;;; contain each indeterminate in X[i] form.
;;;

(defun cocoa-polynomial-ring (n)
  (if (<= n 0) (break "No indeterminates.")
    (if (= n 1) "Q[x[0..0]]"
      (format nil "Q[x[0..~D]]" (1- n)))))

;;;
;;; COCOA-GB-POLYS-FOR-CASE: Given a case, convert its equational polynomials into a form
;;; ready for CoCoA (reducing RHS to 0).
;;;

(defun cocoa-gb-polys (c)
  (let ((eqs (gather-eqs c)))
    (if (not eqs) nil
      (mapcar #'(lambda (l)
		  (let ((cur-x (cadr l))
			(cur-y (caddr l)))
		    (let ((eq-in-lhs-form
			   (if (not (equal cur-y 0)) 
			       `(- ,cur-x ,cur-y)
			     cur-x)))
		      (term-to-qcb eq-in-lhs-form))))
	      eqs))))

;;;
;;; COCOA-GB-TO-ALG-REP: A parser to convert a CoCoA GB to a RAHD alg-rep'd GB.
;;;

(defun cocoa-poly-to-alg-rep (s cocoa-vars-map)
  (poly-prover-rep-to-alg-rep
   (cocoa-poly-to-prover-rep s cocoa-vars-map)))

(defun cocoa-poly-to-prover-rep (s cocoa-vars-map)
  (let* ((intermed-poly-rep (cocoa-parse-poly-to-intermed-rep s cocoa-vars-map))
	 (summands-prover-rep (mapcar #'cocoa-monomial-intermed-rep-to-prover-rep
				      intermed-poly-rep)))
    (if (> (length summands-prover-rep) 1) 
	(term-to-bin-ops (append '(+) summands-prover-rep))
      (term-to-bin-ops (car summands-prover-rep)))))
    
(defun cocoa-monomial-intermed-rep-to-prover-rep (m)

  ;; Note: m is of the form: '(+/- (coeff (POW v_1 n_1) ... (POW v_k n_k)))

  (let ((sign (car m))
	(pp (cadr m)))
    (let ((coeff (car pp))
	  (vp-lst (cdr pp)))
      (cond

       ;; Monomial is only a ground coefficient

       ((not vp-lst) (sign-coeff sign coeff))

       ;; Monomial has only one VP

       ((= (length vp-lst) 1)
	(let* ((vp (car vp-lst))
	       (vp-expanded (expand-var-pow (cadr vp) (caddr vp))))
	  (if (consp vp-expanded)
	      (append `(* ,(sign-coeff sign coeff)) vp-expanded)
	    `(* ,(sign-coeff sign coeff) ,vp-expanded))))

       ;; Monomial has more than one VP

       (t (let ((factors-lst nil))
	    (dolist (vp vp-lst)
	      (setq factors-lst (append (expand-var-pow (cadr vp) (caddr vp))
					factors-lst)))
	    (append `(* ,(sign-coeff sign coeff)) factors-lst)))))))


(defun sign-coeff (sign coeff)
  (if (eql sign '-)
      (- 0 coeff)
    coeff))

(defun expand-var-pow (var pow)
  (let ((out-term nil))
    (case pow
	  (0 (setq out-term '(1)))
	  (1 (setq out-term (list var)))
	  (otherwise 
	   (dotimes (i pow)
	     (setq out-term (cons var out-term)))))
    out-term)) ;; (*) is not included.
   
(defun cocoa-parse-poly-to-intermed-rep (s cocoa-vars-map)
  (let ((poly-token-lst (make-word-lst s))
	(poly-mon-lst nil)
	(cur-sign '+))
    (dolist (tok poly-token-lst)
      (cond ((equal tok "+") (setq cur-sign '+))
	    ((equal tok "-") (setq cur-sign '-))
	    (t (let ((cur-mon (cocoa-parse-monomial tok cocoa-vars-map)))
		 (setq poly-mon-lst
		       (cons `(,cur-sign ,cur-mon) poly-mon-lst))))))
    (reverse poly-mon-lst)))

(defun cocoa-parse-monomial (s cocoa-vars-map)
  (let* ((coeff-pn (cocoa-parse-rational s))
	 (coeff (car coeff-pn))
	 (pp (cocoa-parse-pp (cdr coeff-pn) cocoa-vars-map)))
    (cons (if coeff coeff 1) pp)))

(defun cocoa-parse-pp (s cocoa-vars-map)
  (let ((pp-lst nil)
	(pp-rst s))
    (loop while (not (equal pp-rst "")) do
	  (let* ((cur-vp-pn (cocoa-parse-vp pp-rst cocoa-vars-map))
		 (cur-vp (car cur-vp-pn))
		 (cur-rst (cdr cur-vp-pn)))
	    (setq pp-lst (cons cur-vp pp-lst))
	    (setq pp-rst cur-rst)))
    pp-lst))

(defun cocoa-parse-vp (s cocoa-vars-map)
  (let* ((v-pn (cocoa-parse-var s))
	 (v-id (car v-pn))
	 (v-rst (cdr v-pn))
	 (e-pn (cocoa-parse-expt v-rst))
	 (e-pow (car e-pn))
	 (e-rst (cdr e-pn)))
   #| (format t "v-pn: ~A~% v-id: ~A~% v-rst: ~A~% e-pn: ~A~%  e-pow ~A~%  e-rst ~A~%" 
	    v-pn v-id v-rst e-pn e-pow e-rst) |#
    (cons `(POW ,(aref cocoa-vars-map v-id) ,e-pow) 
	  e-rst)))

(defun cocoa-parse-expt (s)
  (if (equal s "") '(1 . "")
    (let ((pp-c (subseq s 0 1))
	  (pp-expt 1)
	  (rst-s ""))
      (if (equal pp-c "^")
	  (let ((pp-pn (cocoa-parse-rational (subseq s 1))))
	    (setq pp-expt (car pp-pn))
	    (setq rst-s (cdr pp-pn)))
	(setq rst-s s))
      (cons pp-expt rst-s))))

(defun cocoa-parse-var (s)
;  (format t "~A~%" s)
  (if (equal s "") '(nil . "")
    (let ((v-x (subseq s 0 2))
	  (v-x-id nil)
	  (rst-s ""))
      (if (equal v-x "x[")
	  (let ((v-x-pn (cocoa-parse-rational (subseq s 2))))
	    (setq v-x-id (car v-x-pn))
	    (setq rst-s (cdr v-x-pn))
	    (if (equal (subseq rst-s 0 1) "]")
		(setq rst-s (subseq rst-s 1)))))
      (cons v-x-id rst-s))))

;;;
;;; COCOA-PARSE-RATIONAL (s): Given a string beginning with a rational number, "rS," where
;;; S begins with some non-numeric character, return (r . S), where r is a Lisp rational.
;;;

(defun cocoa-parse-rational (s)
  (let* ((parse-num-0 (cocoa-parse-nat s))
	 (numerator (car parse-num-0))
	 (num-0-rst (cdr parse-num-0)))
    (if (and (> (length num-0-rst) 1) 
	     (string-equal (subseq num-0-rst 0 1) "/"))
	(let* ((parse-num-1 (cocoa-parse-nat (subseq num-0-rst 1)))
	       (denominator (car parse-num-1))
	       (num-1-rst (cdr parse-num-1)))
	  (cons (/ numerator denominator) num-1-rst))
      (cons numerator num-0-rst))))
			
;;;
;;; COCOA-PARSE-NAT (s): Given a string beginning with a numeral, "nnn...nS" where S begins
;;; with some non-numeric character, return a list: (nnn...n . S) where nnn...n is "nnn...n" 
;;; converted to a Lisp natural number.
;;;

(defun cocoa-parse-nat (s)
  (let ((num "") (c 0))
    (loop for char across s
	  do (if (not (member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))) (return t)
	       (progn (setq num (concatenate 'string num (string char)))
		      (setq c (1+ c)))))
    (if (> c 0) (cons (parse-integer num) (subseq s c)) `(nil . ,s))))
