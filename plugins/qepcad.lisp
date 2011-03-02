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
;;;            last updated on  02-March-2011.
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
  (cond ((and (not generic) (not (open-conj c))) c)
	((not (all-vars-in-conj c)) c)
	(t (progn
	     (write-open-cad-file c generic)
	     (let ((error-code
		    (#+allegro excl:run-shell-command
			       #+cmu extensions:run-program
			       #+sbcl sb-ext:run-program
			       (prepend-plugins-path "qepcad.bash")
			       #+sbcl nil)))
	       (fmt 3 "~% [Plugin:Qepcad] Qepcad.bash exited with code: ~A. ~%" error-code)
	       (if #+allegro (= error-code 0)
		 #+cmu t  ;;
		 #+sbcl t ;; Need to learn how to get error codes for SBCL and CMUCL.
		 (with-open-file (cad-output (prepend-plugins-path "proofobl.out") :direction :input)
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
		 c))))))

(defun open-conj (c)
  (let ((is-open? t))
    (dolist (lit c)
      (let ((cur-r (car lit)))
	(setq is-open? 
	      (and is-open? 
		   (or (equal cur-r '<) (equal cur-r '>))))))
    is-open?))

;;;
;;; RUN-CAD-ON-ENTIRE-GOAL: Run CAD on an entire top-level *G*.
;;;  Note that this goal, G, must already be processed into RAHD RCF form.
;;;

#+ccl (defun run-cad-on-entire-goal (goal) (declare (ignore goal)) nil)

#+allegro 
(defun run-cad-on-entire-goal (goal)
  (let ((g (tlf-to-bin-ops goal)))
    (let ((vars-in-g nil))
      (dolist (c g)
	(setq vars-in-g (union vars-in-g (all-vars-in-conj c)))
	vars-in-g)
      (let ((cad-cnf "")
	    (count 0))
	(dolist (c g)
	  (setq cad-cnf
		(format nil "~A ~A [~A]"
			cad-cnf
			(if (> count 0) " /\\ " "")
			(disj-to-qcb c nil)))
	  (setq count (1+ count)))

	(let ((cad-input
	       (format nil "[ RAHD top-level Goal ]~%~A~%~A~%~A~%finish.~%"
		       (format nil "(~{~D~#[~:;, ~]~})" vars-in-g)
		       0
		       (format nil "~A[~A]." (ex-quant-prefix vars-in-g) cad-cnf))))

	  (with-open-file (cad-file "proofobl.in.raw" :direction :output :if-exists :supersede)
			  (write-line cad-input cad-file)))

	(let ((start-time (get-internal-real-time)))

	  (let ((error-code
		 (#+allegro excl:run-shell-command
			    #+cmu extensions:run-program
			    "qepcad.bash")))

	    (let* ((end-time (get-internal-real-time))
		   (total-time (float (/ (- end-time start-time) internal-time-units-per-second))))
	    
	      (with-open-file (cad-output "proofobl.out" :direction :input)
			      (let ((cad-decision (read-line cad-output nil)))
				(if (equal cad-decision "\"FALSE\"")
				    (fmt -1 "~% ~A solved by QEPCAD-B from top-level in approx. ~A.~% "
					 *cur-prob* total-time)
				  (fmt -1 "~% ~A _NOT_ solved by QEPCAD-B.  It took approx. ~A for QEPCAD-B to fail on this problem.~%"
				       *cur-prob* total-time)))))))))))


(defun write-open-cad-file (c generic)
  (with-open-file 
   (cad-file (prepend-plugins-path "proofobl.in.raw") 
	     :direction :output :if-exists :supersede)
   (dolist (l (open-cad-input c generic))
     (write-line l cad-file))))

(defun open-cad-input (c generic)
  `("[ RAHD Goal ]"
    ,(open-cad-vars-lst c)
    "0"
    ,(open-cad-conj c generic)
    "finish."))

(defun open-cad-vars-lst (c)
  (let ((all-vars (all-vars-in-conj c)))
    (format nil "(~{~D~#[~:;, ~]~})" all-vars)))

(defun open-cad-conj (c generic)
  (concatenate 
   'string
   (ex-inf-quant-prefix c generic)
   "[" (conj-to-qcb c "") "]."))

(defparameter qp "")

(defun ex-inf-quant-prefix (c generic)
  (let ((all-vars (all-vars-in-conj c)))
    (progn
      (setq qp "")
      (dolist (v all-vars)
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

