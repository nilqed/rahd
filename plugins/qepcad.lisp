;;;
;;; An RAHD plugin for the QEPCAD-B tool
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
;;; This file: began on         31-July-2008       (not as a plugin),
;;;            last updated on  28-April-2011.
;;;

(in-package RAHD)

(defun qepcad-plugin (c &key open?)
  (if open? (open-qepcad c)
    (full-qepcad c)))

;;;
;;; Implementation.
;;;

(defun open-qepcad (c)
  (let ((open-frag (gather-strict-ineqs c)))
    (if open-frag 
	(let ((result (run-qepcad open-frag nil)))
	  (if (or (equal result open-frag) 
		  (equal (car result) ':SAT)) ; Cannot trust :SAT here
	      c
	    result))
    c)))

(defun full-qepcad (c)
  (run-qepcad c t))

(defun run-qepcad (c generic?)
  (cond ((and (not generic?) (not (open-conj c))) c)
	((not (all-vars-in-conj c)) c)
	(t (let ((proc
		  (sb-ext:run-program 
		   "qepcad"
		   '("+N800000" nil)
		   :input :stream
		   :output :stream
		   :wait nil
		   :search t)))
	     (let ((final-out c))
	       (ignore-errors 
		 (unwind-protect
		     (let ((q-in (sb-ext:process-input proc)))
		       (when (eq (sb-ext:process-status proc) ':RUNNING)
			 (mapcar (lambda (x) 
				   (format q-in "~A~%" x) 
				   (fmt 5 "To Qepcad: ~A~%" x)
				   (finish-output q-in) 
				   (finish-output))
				 (open-cad-input c generic?)))
		       (with-open-stream (s (sb-ext:process-output proc))
					 (let ((q-out 
						(loop :for line := (read-line s nil nil)
						      :while line
						      :collect line)))
					   (cond ((some #'(lambda (x) (search "TRUE" x)) q-out)
						  (setq final-out '(:SAT :QEPCAD)))
						 ((some #'(lambda (x) (search "FALSE" x)) q-out)
						  (setq final-out '(:UNSAT :QEPCAD)))
						 (t nil)))))
		   (when proc (sb-ext:process-close proc))))
	       final-out)))))

;; (defun run-qepcad (c generic)
;;   (let ((rahd-pid (sb-posix:getpid)))
;;     (cond ((and (not generic) (not (open-conj c))) c)
;; 	  ((not (all-vars-in-conj c)) c)
;; 	  (t (progn
;; 	       (write-open-cad-file c generic rahd-pid)
;; 	       (sb-ext:run-program (prepend-plugins-path "qepcad.bash")
;; 				   (list (format nil "~A" rahd-pid)))	       
;; 	       (if (not (probe-file (prepend-plugins-path (format nil "~A.qepcad.out" rahd-pid))))
;; 		   c
;; 		 (if #+allegro (= error-code 0)
;; 		   #+cmu t  ;;
;; 		   #+sbcl t ;; Need to learn how to get error codes for SBCL and CMUCL.
;; 		   (with-open-file (cad-output (prepend-plugins-path (format nil "~A.qepcad.out" rahd-pid)) :direction :input)
;; 				     (let ((cad-decision (read-line cad-output nil)))
;; 				       (fmt 10 "~% [Plugin:Qepcad] Qepcad decision: ~A, Generic? ~A. ~%" cad-decision generic)
;; 				       (if (equal cad-decision "\"FALSE\"")
;; 					   (if (not generic)
;; 					       '(:UNSAT (:OPEN-PREDICATE :EX-INF-MANY-RELAXATION :QEPCAD-B-REDUCES-TO-FALSE))
;; 					     '(:UNSAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-FALSE)))				   
;; 					 (if (equal cad-decision "\"TRUE\"")
;; 					     (if (not generic)
;; 						 '(:SAT (:OPEN-PREDICATE :EX-INF-MANY-RELAXATION :QEPCAD-B-REDUCES-TO-TRUE))
;; 					       '(:SAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-TRUE)))
;; 					   c))))
;; 		   c)))))))

(defun open-conj (c)
  (let ((is-open? t))
    (dolist (lit c)
      (let ((cur-r (car lit)))
	(setq is-open? 
	      (and is-open? 
		   (or (equal cur-r '<) (equal cur-r '>))))))
    is-open?))


(defun write-open-cad-file (c generic rahd-pid)
  (with-open-file 
   (cad-file (prepend-plugins-path (format nil "~A.qepcad.in.raw" rahd-pid))
	     :direction :output :if-exists :supersede)
   (dolist (l (open-cad-input c generic))
     (write-line l cad-file))))

(defun open-cad-input (c generic)
  (let ((vars-proj-order
	 (cad-vars-lst c)))
  `("[ RAHD Goal ]"
    ,(format nil "(~{~D~#[~:;, ~]~})" vars-proj-order)
    "0"
    ,(open-cad-conj c generic :vars-lst vars-proj-order)
    "finish.")))

(defun cad-vars-lst (c)
  (let ((vars-lst 
	 (reverse 
	  (mapcar (lambda (x)
		    (nth x *vars-table*))
		  (vs-proj-order-brown
		   (mapcar (lambda (l)
			     `(- ,(cadr l) ,(caddr l)))
			   c))))))
	vars-lst))

(defun open-cad-conj (c generic &key vars-lst)
  (let
  	 ;;
	 ;; This notices if a variable was eliminated
	 ;; in the process of canonicalization used by
	 ;; the proj-order procedure.
	 ;;

      ((var-elimd? (> (length (all-vars-in-conj c))
		      (length vars-lst))))

  (concatenate 
   'string
   (ex-inf-quant-prefix c generic :vars-lst vars-lst)
   "[" (conj-to-qcb c "" :canonicalize-polys? var-elimd?) "].")))

(defparameter qp "")

(defun ex-inf-quant-prefix (c generic &key vars-lst)
  (let ((vars 
	 (if vars-lst vars-lst
	   (cad-vars-lst c))))

    (progn
      (setq qp "")
      (dolist (v vars)
	(setq qp (concatenate 
		  'string 
		  qp 
		  (if (not generic) "(F " "(E ")
		  (format nil "~D" v) ") ")))
      qp)))

(defun ex-quant-prefix (vars)
  (let ((qp ""))
    (dolist (v vars)
      (setq qp (concatenate 
		'string 
		qp 
		"(E "
		(format nil "~D" v) ") ")))
    qp))


    
(defun conj-to-qcb (c result &key canonicalize-polys?)
  (cond ((endp c) result)
	(t (let ((cur-lit (car c)))
	     (conj-to-qcb
	      (cdr c)
	      (concatenate 'string
			   result
			   (lit-to-qcb cur-lit :canonicalize-polys? canonicalize-polys?)
			   (if (consp (cdr c)) " /\\ " ""))
	      :canonicalize-polys? canonicalize-polys?)))))

(defun disj-to-qcb (d result)
  (cond ((endp d) result)
	(t (let ((cur-lit (car d)))
	     (disj-to-qcb
	      (cdr d)
	      (concatenate 'string
			   result
			   (lit-to-qcb cur-lit)
			   (if (consp (cdr d)) " \\/ " "")))))))


(defun lit-to-qcb (lit &key canonicalize-polys?)
  (concatenate 'string
	       "["
	       (let ((cur-r (car lit))
		     (cur-x (cadr lit))
		     (cur-y (caddr lit)))

		 (if canonicalize-polys?

		     (concatenate 'string
				  (term-to-qcb (canonicalize-poly `(- ,cur-x ,cur-y)))
				  " "
				  (write-to-string cur-r)
				  " 0")
		 
		 (concatenate 'string
			      (term-to-qcb cur-x) 
			      " "
			      (write-to-string cur-r)
			      " "
			      (term-to-qcb cur-y))))
	       "]"))


(defun term-to-qcb (term)
  (cond ((equal term nil) "")
	((numberp term) 
	 (if (< term 0) 
	     (format nil "(0 - ~d)" (write-to-string (- (rational term))))
	     (write-to-string (rational term))))
	((varp term) (format nil "~D" term))
	((consp term)
	 (let ((cur-f (car term))
	       (cur-x (cadr term))
	       (cur-y (caddr term)))
	   (concatenate 
	    'string
	    "(" (term-to-qcb cur-x)
	    (if (equal cur-f '*) " " 
	      (format nil " ~d " (write-to-string cur-f)))
	    (term-to-qcb cur-y) ")")))))
		   



;;;
;;; Install the plugin as a cmf.
;;;

(defun install-qepcad ()
  (install-plugin
   :cmf-str "qepcad"
   :cmf-fcn #'qepcad-plugin
   :cmf-args '(open?)
   :cmf-tests '( ( ((> x y) (< y z)) . 
		   (:SAT :QEPCAD) )
		 ( ((> (* x y) y) (= x z) (> z (* x y))) . 
		   (:SAT :QEPCAD) )
		 ( ((> x 10) (< x 11) (> y (* z z)) (>= (* z x) (+ x y))) .
		   (:SAT :QEPCAD) )
		 ( ((> (* x x) y) (< (* x x) y)) .
		   (:UNSAT :QEPCAD) )
		 ( ((> 0
		       (- (* 2 (+ (* X Z) (+ (* X Y) (* Y Z))))
			  (+ (* X X) (+ (* Y Y) (* Z Z)))))
		    (<= X 4) (<= Y 4) (<= Z 4) (<= 2 X) (<= 2 Y) (<= 2 Z)) .
		    (:UNSAT :QEPCAD) )
		 )))

(install-qepcad)

