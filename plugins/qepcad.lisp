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
;;;            last updated on  29-April-2011.
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

(defparameter *persistent-qepcad-process* nil)

(defun cleanup-qepcad-proc ()
  (when (sb-ext:process-p *persistent-qepcad-process*)
    (ignore-errors
      (sb-ext:process-close *persistent-qepcad-process*)
      (sb-ext:process-kill *persistent-qepcad-process* 9)
      (setq *persistent-qepcad-process* nil))))

(defun run-qepcad (c generic? &key disj? close-proc?)
  (when (or (not *persistent-qepcad-process*)
	    (not (eq (sb-ext:process-status *persistent-qepcad-process*)
		     ':RUNNING)))
    (setq *persistent-qepcad-process*
	  (sb-ext:run-program 
	   "qepcad"
	   '("+N8000000" nil)
	   :input :stream
	   :output :stream
	   :wait nil
	   :search t)))
  (cond ((and (not disj?) (not generic?) (not (open-conj c))) c)
	((and (not disj?) (not (all-vars-in-conj c))) c)
	(t (let ((proc *persistent-qepcad-process*))
	     (let ((final-out c))
	       (ignore-errors
		 (unwind-protect
		     (let ((q-in (sb-ext:process-input proc)))
		       (when (eq (sb-ext:process-status proc) ':RUNNING)
			 (mapcar (lambda (x) 
				   (fmt 5 "To Qepcad: ~A~%" x)
				   (finish-output)
				   (format q-in "~A~%" x) 
				   (finish-output q-in))
				 (open-cad-input c generic? :disj? disj?)))
		       (let ((s (sb-ext:process-output proc)))
			 (let ((q-out))
			   (loop :for line := (read-line s nil nil)
                                 :while line
				 :until (progn
					  (setq q-out line)
					  ;(fmt 0 "~% Line is ~A.~%" q-out)
					  (or (search "TRUE" line)
					      (search "FALSE" line)
					      (search "FAIL" line)
					      ;(not (eq (sb-ext:process-status *persistent-qepcad-process*)
					      ;':RUNNING))
					      )))
			   (cond ((search "TRUE" q-out)
				  (setq final-out '(:SAT :QEPCAD)))
				 ((search "FALSE" q-out)
				  (setq final-out '(:UNSAT :QEPCAD)))
				 (t c)))))
		   (when (and proc close-proc?) 
		     (cleanup-qepcad-proc))))
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

(defun open-cad-input (c generic &key disj?)
  (let ((vars-proj-order
	 (cad-vars-lst (if disj? (extract-lits c) c))))
  `("[ RAHD Goal ]"
    ,(format nil "(~{~D~#[~:;, ~]~})" vars-proj-order)
    "0"
    ,(open-cad-conj c generic :vars-lst vars-proj-order :disj? disj?)
    "go
go
go
solution T
continue
")))

(defparameter *do-not-proj-order-vars?* nil)

(defun cad-vars-lst (c)
  (let ((vars-lst
	 (if *do-not-proj-order-vars?*
	     (all-vars-in-conj c)
	   (reverse 
	    (mapcar (lambda (x)
		      (nth x *vars-table*))
		    (vs-proj-order-brown
		     (mapcar (lambda (l)
			       `(- ,(cadr l) ,(caddr l)))
			     c)))))))
	vars-lst))

;;;
;;; We now allow disjunctive formulas to be passed to QEPCAD here.
;;;

(defun open-cad-conj (c generic &key vars-lst disj?)
  (let
  	 ;;
	 ;; This notices if a variable was eliminated
	 ;; in the process of canonicalization used by
	 ;; the proj-order procedure.
	 ;;

      ((var-elimd? (> (length (all-vars-in-conj 
			       (if disj? (extract-lits c) c)))
		      (length vars-lst))))

  (concatenate 
   'string
   (ex-inf-quant-prefix c generic :vars-lst vars-lst)
   "[" (if disj?
	   (fml-to-qcb c :canonicalize-polys? var-elimd?)
	 (conj-to-qcb c "" :canonicalize-polys? var-elimd?)) "].")))


;;;
;;; If we're given a general formula which contains a disjunction,
;;;  we want to just pass it through to QEPCAD.
;;;

(defun fml-to-qcb (fml &key canonicalize-polys?)
  (cond ((not (consp fml)) (format nil "~D" fml))
	((eq (car fml) 'AND)
	 (format nil "[~A /\\ ~A]"
		 (fml-to-qcb (cadr fml) :canonicalize-polys? canonicalize-polys?)
		 (fml-to-qcb (caddr fml) :canonicalize-polys? canonicalize-polys?)))
	((eq (car fml) 'OR)
	 (format nil "[~A \\/ ~A]"
		 (fml-to-qcb (cadr fml) :canonicalize-polys? canonicalize-polys?)
		 (fml-to-qcb (caddr fml) :canonicalize-polys? canonicalize-polys?)))
	((eq (car fml) 'NOT)
	 (format nil "[~~ ~A]" 
		 (fml-to-qcb (cadr fml) :canonicalize-polys? canonicalize-polys?)))
	((member (car fml) '(> >= = <= <))
	 (format nil "~A"
		 (lit-to-qcb fml :canonicalize-polys? canonicalize-polys?)))
	(t (error "Bad formula for FML-TO-QCB"))))


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
;;; Extract literals from a general formula 
;;;  (the kind the top-level parser returns).
;;;

(defun extract-lits (f)
  (cond ((not (consp f)) nil)
	((member (car f) '(AND OR))
	 (union (extract-lits (cadr f))
		(extract-lits (caddr f))))
	((eq (car f) 'NOT)
	 (extract-lits (cadr f)))
	(t (list f))))

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

