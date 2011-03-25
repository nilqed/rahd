;;;
;;; RAHD experimental benchmarking for comparing proof strategies.
;;;
;;; Grant Olney Passmore
;;;  Began on: 25-March-2011          Last modified: 25-March-2011
;;;

;;;
;;; Probs-lst-to-array: Given a list of strings read from a problems
;;;  file, convert it into an array of problems, with each member
;;;  of the array being a pair of variable and formula strings.
;;;

(defun probs-lst-to-array (probs)
  (let* ((filtered-probs (remove-if #'(lambda (x) 
					(equal (string-trim '(#\Space) x) ""))
				    probs))
	 (probs-array
	  (make-array (/ (length filtered-probs) 2))))
    (loop for i from 1 to (/ (length filtered-probs) 2) do
	  (let ((v (car filtered-probs))
		(f (cadr filtered-probs)))
	    (setf (aref probs-array (1- i))
		  (cons v f))
	    (setq filtered-probs (cddr filtered-probs))))
    probs-array))

;;;
;;; Probs-array: Build an array of problems from a problem file.
;;;

(defun build-probs-array (&key filename)
  (with-open-file (prob-stream filename)
		  (loop for prob = (read-line prob-stream nil nil)
			until (eq prob nil)
			collect prob into probs
			finally (return (probs-lst-to-array probs)))))

;;;
;;; Benchmark: Given a file containing problems (two lines per problem,
;;;  the first line is a list of variables, the second is the formula), 
;;;  and a list of strategies, 

(defun benchmark (&key filename strategy-ids)
  (let ((probs-array (build-probs-array :filename filename)))
    (dolist (strategy-id strategy-ids)
      (loop for i from 0 to 1000 ;(1- (length probs-array)) do
	    do (let* ((cur-prob (aref probs-array i))
		      (cur-v (car cur-prob))
		      (cur-f (cdr cur-prob)))
		 (fmt 0 "~A, ~A, ~A, " i strategy-id cur-v)
		 (let ((start-time (get-internal-run-time)))
		   (let ((proc
			  (sb-ext:run-program 
			   "/Users/grant/Research/Programs/MyCode/rahd/benchrun.bash"
			   `("-v" ,cur-v "-f" ,cur-f "-run-strat"
			     ,(format nil "~A" strategy-id)
			     "-print-model")
			   :output :stream
			   :search t)))
		     (let ((end-time (get-internal-run-time)))
		       (fmt 0 "~A, " (float (/ (- end-time start-time) internal-time-units-per-second)))
		       (with-open-stream (s (sb-ext:process-output proc))
					 (let ((rahd-out
						(loop :for line := (read-line s nil nil)
					     :while line
					     :collect line)))
					   (cond ((some #'(lambda (x) (search " unsat" x)) rahd-out)
						  (fmt 0 "unsat~%"))
						 ((some #'(lambda (x) (search " model:" x)) rahd-out)
						  (fmt 0 "sat-model~%"))
						 ((some #'(lambda (x) (search " sat" x)) rahd-out)
						  (fmt 0 "sat~%"))
						 ((some #'(lambda (x) (search " unknown" x)) rahd-out)
						  (fmt 0 "unknown~%"))
						 (t (fmt 0 "timeout~%")))))))))))))

;;;
; How to invoke:
;
; (benchmark :filename "/Users/grant/.rahd/problems.log" :strategy-ids '(0 1 2 3 4 5 6 7 8 9 10 11 12))
;
;;;