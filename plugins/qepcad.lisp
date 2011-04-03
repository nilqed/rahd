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
;;;            last updated on  03-April-2011.
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

(defun run-qepcad (c generic)
  (let ((rahd-pid (sb-posix:getpid)))
    (cond ((and (not generic) (not (open-conj c))) c)
	  ((not (all-vars-in-conj c)) c)
	  (t (progn
	       (write-open-cad-file c generic rahd-pid)
	       (sb-ext:run-program (prepend-plugins-path "qepcad.bash")
				   (list (format nil "~A" rahd-pid)))	       
	       (if (not (probe-file (prepend-plugins-path (format nil "~A.qepcad.out" rahd-pid))))
		   c
		 (if #+allegro (= error-code 0)
		   #+cmu t  ;;
		   #+sbcl t ;; Need to learn how to get error codes for SBCL and CMUCL.
		   (with-open-file (cad-output (prepend-plugins-path (format nil "~A.qepcad.out" rahd-pid)) :direction :input)
				     (let ((cad-decision (read-line cad-output nil)))
				       (fmt 10 "~% [Plugin:Qepcad] Qepcad decision: ~A, Generic? ~A. ~%" cad-decision generic)
				       (if (equal cad-decision "\"FALSE\"")
					   (if (not generic)
					       '(:UNSAT (:OPEN-PREDICATE :EX-INF-MANY-RELAXATION :QEPCAD-B-REDUCES-TO-FALSE))
					     '(:UNSAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-FALSE)))				   
					 (if (equal cad-decision "\"TRUE\"")
					     (if (not generic)
						 '(:SAT (:OPEN-PREDICATE :EX-INF-MANY-RELAXATION :QEPCAD-B-REDUCES-TO-TRUE))
					       '(:SAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-TRUE)))
					   c))))
		   c)))))))

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
  (concatenate 
   'string
   (ex-inf-quant-prefix c generic :vars-lst vars-lst)
   "[" (conj-to-qcb c "") "]."))

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

(defparameter all-vars nil)

(defun all-vars-in-conj (c)
  (setq all-vars nil)
  (dolist (lit c)
    (let ((use-lit 
	   (if (equal (car lit) 'NOT)
	       (cadr lit)
	     lit)))
      (setq all-vars 
	    (union all-vars
		   (union 
		    (gather-vars (cadr use-lit))
		    (gather-vars (caddr use-lit)))))))
    all-vars)
    
(defun conj-to-qcb (c result)
  (cond ((endp c) result)
	(t (let ((cur-lit (car c)))
	     (conj-to-qcb
	      (cdr c)
	      (concatenate 'string
			   result
			   (lit-to-qcb cur-lit)
			   (if (consp (cdr c)) " /\\ " "")))))))

(defun disj-to-qcb (d result)
  (cond ((endp d) result)
	(t (let ((cur-lit (car d)))
	     (disj-to-qcb
	      (cdr d)
	      (concatenate 'string
			   result
			   (lit-to-qcb cur-lit)
			   (if (consp (cdr d)) " \\/ " "")))))))


(defun lit-to-qcb (lit)
  (concatenate 'string
	       "["
	       (let ((cur-r (car lit))
		     (cur-x (cadr lit))
		     (cur-y (caddr lit)))
		 (concatenate 'string
			      (term-to-qcb cur-x) 
			      " "
			      (write-to-string cur-r)
			      " "
			      (term-to-qcb cur-y)))
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
		   
(defun varp (term)
  (and (symbolp term)
       (not (equal term '=))
       (not (equal term '>))
       (not (equal term '<))
       (not (equal term '<=))
       (not (equal term '>=))))


;;;
;;; Install the plugin as a cmf.
;;;

(install-plugin
 :cmf-str "qepcad"
 :cmf-fcn #'qepcad-plugin
 :cmf-args '(open?)
 :cmf-tests '( ( ((> x y) (< y z)) . 
		 (:SAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-TRUE)) )
	       ( ((> (* x y) y) (= x z) (> z (* x y))) . 
		 (:SAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-TRUE)) )
	       ( ((> x 10) (< x 11) (> y (* z z)) (>= (* z x) (+ x y))) .
		 (:SAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-TRUE)) )
	       ( ((> (* x x) y) (< (* x x) y)) .
		 (:UNSAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-FALSE)) )
	       ( ((> 0
		     (- (* 2 (+ (* X Z) (+ (* X Y) (* Y Z))))
			(+ (* X X) (+ (* Y Y) (* Z Z)))))
		  (<= X 4) (<= Y 4) (<= Z 4) (<= 2 X) (<= 2 Y) (<= 2 Z)) .
		 (:UNSAT (:GENERIC-PREDICATE :QEPCAD-B-REDUCES-TO-FALSE)) )		 
	       ))

