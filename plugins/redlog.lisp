;;;
;;; A RAHD plugin for the Reduce/Redlog tool
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
;;; This file: began on         24-February-2011       (before, was part of 
;;;            last updated on  24-February-2011.          qepcad.lisp)
;;;

;;;
;;; Given a case and an optional list of variables, run Redlog's VTS engine
;;;  to eliminate the given variables (or all variables if none are given)
;;;  from the existential closure of the case.
;;;

(defun redlog-vts-plugin (c &key vars)
  (let* ((rahd-pid (sb-posix:getpid))
	 (case-to-redlog
	  (goal-to-redlog 
	   (mapcar #'list c)))
	 (out-str
	  (format nil 
"% RAHD<->Redlog plugin generated problem
load_package redlog;
rlset ofsf;
off nat;
off echo;
~A
result := rlqe phi;
out \"./plugins/~A.redlog.out\";
write result;
shut \"./plugins/~A.redlog.out\";
quit;"
case-to-redlog
rahd-pid
rahd-pid)))

    ;;
    ;; Write Redlog input to file
    ;;

    (with-open-file 
     (redlog-file (prepend-plugins-path (format nil "~A.redlog.in" rahd-pid))
		  :direction :output :if-exists :supersede)
     (write-line out-str redlog-file))

    ;;
    ;; Execute redlog.bash with RAHD pid as argument.
    ;;

    (sb-ext:run-program (prepend-plugins-path "redlog.bash")
			(list (format nil "~A" rahd-pid)))

    ;;
    ;; Result of Redlog was written to <rahd-pid>.redlog.out, 
    ;;  so let's read it back.
    ;;
    ;; Right now, we'll just go for an endgame solver and
    ;;  read back true or false.
    ;;

    (let ((result))

      (with-open-file
       (redlog-file (prepend-plugins-path (format nil "~A.redlog.out.final" rahd-pid))
		    :direction :input)
       (let ((rl (read-line redlog-file nil)))
	 (if (equal rl "false$")
	     (setq result ':UNSAT)
	   (if (equal rl "true$")
	       (setq result ':SAT))))

       (cond ((equal result ':UNSAT)
	      '(:UNSAT :REDLOG-RLQE))
	     ((equal result ':SAT)
	      '(:SAT :REDLOG-RLQE))
	     (t c))))))

;;;
;;; Install the plugin as a cmf.
;;;

(install-plugin
 :cmf-str "redlog-vts"
 :cmf-fcn #'redlog-vts-plugin
 :cmf-args '(vars))

;;;
;;; Functions for exporting REDLOG input.
;;;

(defun goal-to-redlog (goal)
  (let ((g (tlf-to-bin-ops goal)))
    (let ((vars-in-g nil))
      (dolist (c g)
	(setq vars-in-g (union vars-in-g (all-vars-in-conj c)))
	vars-in-g)
      (let ((redlog-formula "")
	    (count 0))
	(dolist (c g)
	  (setq redlog-formula
		(format nil "~A~% phi~A := ~A;"
			redlog-formula
			count
			(disj-to-redlog c "")))
	  (setq count (1+ count)))
	(format nil "~A~% phi := ex({~{~D~#[~:;, ~]~}}, ~A);" 
		redlog-formula 
		vars-in-g 
		(let ((out ""))
		  (loop for i from 0 to (1- count) do
			(setq out (format nil "~A~Aphi~A"
					out (if (> i 0) " and " "") i)))
		  out))))))


(defun term-to-redlog (term)
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
	    "(" (term-to-redlog cur-x)
	    (format nil " ~d " (write-to-string cur-f))
	    (term-to-redlog cur-y) ")")))))

(defun disj-to-redlog (d result)
  (cond ((endp d) result)
	(t (let ((cur-lit (car d)))
	     (let ((use-lit (if (equal (car cur-lit) 'NOT)
				(cadr cur-lit)
			      cur-lit)))
	     (disj-to-redlog
	      (cdr d)
	      (format nil "~A~A~A~A"
		      result
		      (if (not (equal use-lit cur-lit))
			  "not" "")
		      (lit-to-redlog use-lit)
		      (if (consp (cdr d)) " or " ""))))))))

(defun lit-to-redlog (lit)
  (concatenate 'string
	       "("
	       (let ((cur-r (car lit))
		     (cur-x (cadr lit))
		     (cur-y (caddr lit)))
		 (concatenate 'string
			      (term-to-redlog cur-x) 
			      " "
			      (write-to-string cur-r)
			      " "
			      (term-to-redlog cur-y)))
	       ")"))