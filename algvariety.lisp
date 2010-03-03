;;;
;;; A procedure for translating semialgebraic definitions to equivalent definitions
;;; that are purely equational.  Note, this uses the RCF corpus format, not the
;;; internal NLRAP format as in polyalg.lisp.
;;;
;;; We use the following Seidenberg equivalences:
;;;
;;;  s  <=  t      :<=>      (E x)[        t = s + x^2  ]
;;;  s  <   t      :<=>      (E x)[ (t-s)x^2 = 1        ]
;;;  s  !=  t      :<=>      (E x)[ (t-s)x   = 1        ]
;;;
;;; Grant Olney Passmore
;;; 21-July-2008
;;;

(defparameter *vars*
  '(A B C D E F G H I J K L M N O P Q R S T U V W X Z Y))

(defun conv-rahd-case (c)
  (let ((eq-c nil)
	(usable-vars (usable-vars c)))
    (dolist (l c)
      (setq eq-c (cons (conv-constraint l (car usable-vars)) eq-c))
      (setq usable-vars (cdr usable-vars)))
    eq-c))
    

(defun extract-vars (f)
  (cond ((endp f) nil)
	(t (let ((cur-sf (car f)))
	     (cond ((stringp cur-sf)
		    (extract-vars (cdr f)))
		   ((equal (car cur-sf) 'DEFINE)
		    (cons (cadr cur-sf) (extract-vars (cdr f))))
		   (t nil))))))

(defun usable-vars (f)
  (set-difference *vars* (extract-vars f)))

(defun conv-constraint (c v)
  (let ((r (car c)))
    (cond ((equal r 'NOT)
	   (let ((params (cdadr c)))
	     (case (caadr c)
		   (>= (conv-constraint (list* '< params) v))
		   (<= (conv-constraint (list* '> params) v))
		   (>  (conv-constraint (list* '<= params) v))
		   (<  (conv-constraint (list* '>= params) v))
		   (=  (let ((x (cadadr c)) (y (car (cddadr c))))
			 `(= (- (* (- ,x ,y) ,v) 1) 0))))))
	  (t (let ((x (cadr c)) (y (caddr c)))
	       (case r
		     (>= `(= (- (+ ,y (* ,v ,v)) ,x) 0))
		     (<= `(= (- (+ ,x (* ,v ,v)) ,y) 0))
		     (>  `(= (- (* (- ,x ,y) (* ,v ,v)) 1) 0))
		     (<  `(= (- (* (- ,y ,x) (* ,v ,v)) 1) 0))
		     (=   (cond ((equal y 0) c)
				((equal x 0) `(= ,y 0))
				(t `(= (- ,x ,y) 0))))))))))
			
;;;
;;; This conversion function assumes that the assertions are atomic, e.g.
;;; they do not contain a top-level disjunction.
;;;
;;; Note: CONV-FORMULA works on the RCF/Yices2 corpus format that is presented
;;;  with (ASSERT ...) and (DEFINE ...).

(defun conv-formula* (f vs)
  (cond ((endp f) nil)
	((endp vs) (break "Error: Out of fresh variables!"))
	(t (let ((cur-f (car f)))
	     (if (stringp cur-f) (conv-formula* (cdr f) vs)
	       (let ((cur-a (car cur-f)))
		 (cond ((equal cur-a 'DEFINE)
			(conv-formula* (cdr f) vs))
		       ((equal cur-a 'ASSERT)
			(cons (conv-constraint (cadr cur-f) (car vs))
			      (conv-formula* (cdr f) (cdr vs)))))))))))

(defun conv-formula (f)
  (conv-formula* f (reverse (usable-vars f))))

;;;
;;; Print formula for GFAN style input.
;;;

(defun printf-gf (f)
  (cond ((endp f) nil)
	(t (cons
	    (printsf-gf (car f)) 	    
	    (printf-gf (cdr f))))))

(defun printsf-gf (sf)
  (cond ((equal sf nil) "")
	((symbolp sf) (symbol-name sf))
	((numberp sf) (write-to-string sf))
	(t (let ((cur-op (car sf))
		 (cur-x  (cadr sf))
		 (cur-y  (caddr sf)))
	     (case cur-op
		   (= (concatenate 
		       'string 
		       (printsf-gf cur-x) 
		       "  =  " 
		       (printsf-gf cur-y)))
		   (* (concatenate
		       'string
		       (printsf-gf cur-x) (printsf-gf cur-y)))
		   (- (concatenate
		       'string
		       "(" (printsf-gf cur-x) " - (" (printsf-gf cur-y) "))"))
		   (+ (cond ((equal cur-x 0)
			     (printsf-gf cur-y))
			    ((equal cur-y 0)
			     (printsf-gf cur-x))
			    (t (concatenate
				'string
				(printsf-gf cur-x) " + " (printsf-gf cur-y))))))))))
	

(defun clear-bad-vars (f)
  (let ((vs (reverse (usable-vars f))))
    (subst (car vs) 'A1
	   (subst (cadr vs) 'A2
		  (subst (caddr vs) 'B1
			 (subst (cadddr vs) 'B2 f))))))


(defun make-equational (f)
  (printf-gf (conv-formula (clear-bad-vars f))))

#|
Examples:

(conv-constraint '(NOT (>= (- (* A1 A2) (* B1 B2)) 0)) 'x)

|#
