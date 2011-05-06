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
      (loop for i from 0 to (1- (length probs-array))
	    do (let* ((cur-prob (aref probs-array i))
		      (cur-v (car cur-prob))
		      (cur-f (cdr cur-prob)))
		 (fmt 0 "~A, ~A, ~A, " i strategy-id cur-v)
		 (let ((start-time (get-internal-real-time)))
		   (let ((proc
			  (sb-ext:run-program 
			   "/Users/grant/Research/Programs/MyCode/rahd/benchrun.bash"
			   `("-v" ,cur-v "-f" ,cur-f "-run-strat"
			     ,(format nil "~A" strategy-id)
			     "-print-model")
			   :output :stream
			   :search t)))
		     (let ((end-time (get-internal-real-time)))
		       (fmt 0 "~$, " (float (/ (- end-time start-time) internal-time-units-per-second)))
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

(defun print-cmf-counts (p-id p-cch)
  (fmt 0 "~% ~A:~%" p-id)
  (maphash (lambda (x y)
	     (fmt 0 "~%    ~A --> ~A"
		  x y))
	  p-cch))

(defun print-prob-cmf-counts (cchh)
  (maphash
   (lambda (p-id p-cch)
     (print-cmf-counts p-id p-cch))
   cchh))

;;;
;;
;; New benchmarking of different strategies on calculemus problems.
;;
;;;

(defun calculemus-benchmark (&key strategy-ids (verbosity 0) (problem-ids))
  (let ((probs-lst (mapcar #'car *calculemus-suite*)) (i 0)
	(cmf-count-hash-hash (make-hash-table :test 'eq)))
    (dolist (strategy-id strategy-ids)
      (setq i 0)
      (dolist (cur-prob probs-lst)
	(clrhash *cmf-count-hash*)
	(when (or (not problem-ids)
		  (member i problem-ids))
	  (fmt 0 "~A, ~A, " i strategy-id)
	  (let ((start-time (get-internal-real-time)))
	    (let ((result
		   (progn
		     (rahd-reset-state)
		     (check cur-prob
			    :print-model nil
			    :verbosity verbosity
			    :strategy `(run ,(get-strat-by-num strategy-id))
			    :non-recursive? nil))))
	      (let ((end-time (get-internal-real-time)))
		(fmt 0 "~A,~A~%"
		     (float (/ (- end-time start-time) internal-time-units-per-second))
		     result))))
	  (fmt 0 " Prob: ~A" i)
	  (maphash (lambda (x y) (fmt 0 "~%   ~A --> ~A" x y)) *cmf-count-hash*)
	  (fmt 0 "~%~%")
	  (setf (gethash i cmf-count-hash-hash) *cmf-count-hash*))
	(setq i (1+ i))))))

(defparameter *calculemus-suite* 
'(

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 0 in RAHD format
;;;

 ( (((>= A 0)) ((<= A 1)) ((>= B 0)) ((<= B 1)) ((>= C 0)) ((<= C 1))
    ((>= D 0)) ((<= D 1)) ((>= E 0)) ((<= E 1))
    ((< (+ (* 21 (* B (* B (* B B))))
           (+ (* -84 (* C (* B (* B B))))
              (+ (* 126 (* (* C C) (* B B)))
                 (+ (* -84 (* (* C (* C C)) B))
                    (+ (* 21 (* C (* C (* C C))))
                       (+ (* A A)
                          (+ (* B A)
                             (+ (* -2 (* C A))
                                (+
                                 (* C C)
                                 (+
                                  (* D D)
                                  (+
                                   (* -2 (* E D))
                                   (+ (* E E) (+ A D)))))))))))))
        0))) 
 :UNSAT ) 

;;;
;;; Problem 0 in Redlog format
;;;

#|

 phi0 := (((21 * (B * (B * (B * B)))) + (((0 - 84) * (C * (B * (B * B)))) + ((126 * ((C * C) * (B * B))) + (((0 - 84) * ((C * (C * C)) * B)) + ((21 * (C * (C * (C * C)))) + ((A * A) + ((B * A) + (((0 - 2) * (C * A)) + ((C * C) + ((D * D) + (((0 - 2) * (E * D)) + ((E * E) + (A + D))))))))))))) < 0);
 phi1 := (E <= 1);
 phi2 := (E >= 0);
 phi3 := (D <= 1);
 phi4 := (D >= 0);
 phi5 := (C <= 1);
 phi6 := (C >= 0);
 phi7 := (B <= 1);
 phi8 := (B >= 0);
 phi9 := (A <= 1);
 phi10 := (A >= 0);
 phi := ex({B, C, E, D, A}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8 and phi9 and phi10); 

|#
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 1 in RAHD format
;;;

 ( (((>= A 0)) ((<= A 1)) ((>= B 0)) ((<= B 1)) ((>= C 0)) ((<= C 1))
    ((>= D 0)) ((<= D 1)) ((>= E 0)) ((<= E 1))
    ((= F 0) (= F 1) (= F 2))
    ((< (+ F
           (+ (* (* A A) B)
              (+ (* C (* C (* C C)))
                 (+ (* -2 (* A (* C C)))
                    (+ (* E E)
                       (+ (* -2 (* D E))
                          (+ (* D D)
                             (+ (* 3 (* C C))
                                (+
                                 (* -6 (* B C))
                                 (+
                                  (* 3 (* B B))
                                  (+ (* A A) (+ D 1))))))))))))
        0))) 
 :UNSAT ) 

;;;
;;; Problem 1 in Redlog format
;;;

#| 

 phi0 := ((F + (((A * A) * B) + ((C * (C * (C * C))) + (((0 - 2) * (A * (C * C))) + ((E * E) + (((0 - 2) * (D * E)) + ((D * D) + ((3 * (C * C)) + (((0 - 6) * (B * C)) + ((3 * (B * B)) + ((A * A) + (D + 1)))))))))))) < 0);
 phi1 := (F = 2) or (F = 1) or (F = 0);
 phi2 := (E <= 1);
 phi3 := (E >= 0);
 phi4 := (D <= 1);
 phi5 := (D >= 0);
 phi6 := (C <= 1);
 phi7 := (C >= 0);
 phi8 := (B <= 1);
 phi9 := (B >= 0);
 phi10 := (A <= 1);
 phi11 := (A >= 0);
 phi := ex({F, E, C, B, D, A}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8 and phi9 and phi10 and phi11); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 2 in RAHD format
;;;

 ( (((>= A 1)) ((<= A 2)) ((>= B 1)) ((<= B 2)) ((>= C 1)) ((<= C 2))
    ((>= D 1)) ((<= D 2)) ((= E 1) (= E 2) (= E 3))
    ((< (+ (* 2 (* (* C C) (* E E)))
           (+ (* 3 (* (* B B) (* C C)))
              (+ (* -6 (* (* B (* B B)) C))
                 (+ (* 3 (* B (* B (* B B))))
                    (+ (* -4 (* A (* C (* E E))))
                       (+ (* -4 (* A (* (* C C) E)))
                          (+ (* -6 (* A (* B (* C C))))
                             (+ (* 12 (* A (* (* B B) C)))
                                (+
                                 (* -6 (* A (* B (* B B))))
                                 (+
                                  (* 2 (* (* A A) (* E E)))
                                  (+
                                   (* 8 (* (* A A) (* C E)))
                                   (+
                                    (* 6 (* (* A A) (* C C)))
                                    (+
                                     (* -6 (* (* A A) (* B C)))
                                     (+
                                      (* 3 (* (* A A) (* B B)))
                                      (+
                                       (* -4 (* (* A (* A A)) E))
                                       (+
                                        (* -4 (* (* A (* A A)) C))
                                        (+
                                         (* 2 (* A (* A (* A A))))
                                         (+
                                          (* E E)
                                          (+
                                           (* -2 (* D E))
                                           (+
                                            (* D D)
                                            (+
                                             D
                                             (*
                                              7
                                              C))))))))))))))))))))))
        0))) 
 :UNSAT ) 

;;;
;;; Problem 2 in Redlog format
;;;

 #|

 phi0 := (((2 * ((C * C) * (E * E))) + ((3 * ((B * B) * (C * C))) + (((0 - 6) * ((B * (B * B)) * C)) + ((3 * (B * (B * (B * B)))) + (((0 - 4) * (A * (C * (E * E)))) + (((0 - 4) * (A * ((C * C) * E))) + (((0 - 6) * (A * (B * (C * C)))) + ((12 * (A * ((B * B) * C))) + (((0 - 6) * (A * (B * (B * B)))) + ((2 * ((A * A) * (E * E))) + ((8 * ((A * A) * (C * E))) + ((6 * ((A * A) * (C * C))) + (((0 - 6) * ((A * A) * (B * C))) + ((3 * ((A * A) * (B * B))) + (((0 - 4) * ((A * (A * A)) * E)) + (((0 - 4) * ((A * (A * A)) * C)) + ((2 * (A * (A * (A * A)))) + ((E * E) + (((0 - 2) * (D * E)) + ((D * D) + (D + (7 * C)))))))))))))))))))))) < 0);
 phi1 := (E = 3) or (E = 2) or (E = 1);
 phi2 := (D <= 2);
 phi3 := (D >= 1);
 phi4 := (C <= 2);
 phi5 := (C >= 1);
 phi6 := (B <= 2);
 phi7 := (B >= 1);
 phi8 := (A <= 2);
 phi9 := (A >= 1);
 phi := ex({B, A, C, E, D}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8 and phi9); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 3 in RAHD format
;;;

 ( (((>= A 1)) ((<= A 2)) ((>= B 1)) ((<= B 2)) ((>= C 1)) ((<= C 2))
    ((>= D 1)) ((<= D 2)) ((= E 1) (= E 2) (= E 3))
    ((< (+ (* 2 (* (* C C) (* E E)))
           (+ (* 3 (* (* B B) (* C C)))
              (+ (* -6 (* (* B (* B B)) C))
                 (+ (* 3 (* B (* B (* B B))))
                    (+ (* -4 (* A (* C (* E E))))
                       (+ (* -4 (* A (* (* C C) E)))
                          (+ (* -6 (* A (* B (* C C))))
                             (+ (* 12 (* A (* (* B B) C)))
                                (+
                                 (* -6 (* A (* B (* B B))))
                                 (+
                                  (* 2 (* (* A A) (* E E)))
                                  (+
                                   (* 8 (* (* A A) (* C E)))
                                   (+
                                    (* 6 (* (* A A) (* C C)))
                                    (+
                                     (* -6 (* (* A A) (* B C)))
                                     (+
                                      (* 3 (* (* A A) (* B B)))
                                      (+
                                       (* -4 (* (* A (* A A)) E))
                                       (+
                                        (* -4 (* (* A (* A A)) C))
                                        (+
                                         (* 2 (* A (* A (* A A))))
                                         (+
                                          (* E E)
                                          (+
                                           (* -2 (* D E))
                                           (+
                                            (* D D)
                                            (+
                                             D
                                             (*
                                              7
                                              C))))))))))))))))))))))
        1))) 
 :UNSAT ) 

;;;
;;; Problem 3 in Redlog format
;;;

#|

 phi0 := (((2 * ((C * C) * (E * E))) + ((3 * ((B * B) * (C * C))) + (((0 - 6) * ((B * (B * B)) * C)) + ((3 * (B * (B * (B * B)))) + (((0 - 4) * (A * (C * (E * E)))) + (((0 - 4) * (A * ((C * C) * E))) + (((0 - 6) * (A * (B * (C * C)))) + ((12 * (A * ((B * B) * C))) + (((0 - 6) * (A * (B * (B * B)))) + ((2 * ((A * A) * (E * E))) + ((8 * ((A * A) * (C * E))) + ((6 * ((A * A) * (C * C))) + (((0 - 6) * ((A * A) * (B * C))) + ((3 * ((A * A) * (B * B))) + (((0 - 4) * ((A * (A * A)) * E)) + (((0 - 4) * ((A * (A * A)) * C)) + ((2 * (A * (A * (A * A)))) + ((E * E) + (((0 - 2) * (D * E)) + ((D * D) + (D + (7 * C)))))))))))))))))))))) < 1);
 phi1 := (E = 3) or (E = 2) or (E = 1);
 phi2 := (D <= 2);
 phi3 := (D >= 1);
 phi4 := (C <= 2);
 phi5 := (C >= 1);
 phi6 := (B <= 2);
 phi7 := (B >= 1);
 phi8 := (A <= 2);
 phi9 := (A >= 1);
 phi := ex({B, A, C, E, D}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8 and phi9); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 4 in RAHD format
;;;

 ( (((>= A 0)) ((<= A 1)) ((>= B 0)) ((<= B 1)) ((>= C 0)) ((<= C 1))
    ((>= D 0)) ((<= D 1)) ((= E 0) (= E 1) (= E 2))
    ((< (+ (* 2 (* (* C C) (* E E)))
           (+ (* 3 (* (* B B) (* C C)))
              (+ (* -6 (* (* B (* B B)) C))
                 (+ (* 3 (* B (* B (* B B))))
                    (+ (* -4 (* A (* C (* E E))))
                       (+ (* -4 (* A (* (* C C) E)))
                          (+ (* -6 (* A (* B (* C C))))
                             (+ (* 12 (* A (* (* B B) C)))
                                (+
                                 (* -6 (* A (* B (* B B))))
                                 (+
                                  (* 2 (* (* A A) (* E E)))
                                  (+
                                   (* 8 (* (* A A) (* C E)))
                                   (+
                                    (* 6 (* (* A A) (* C C)))
                                    (+
                                     (* -6 (* (* A A) (* B C)))
                                     (+
                                      (* 3 (* (* A A) (* B B)))
                                      (+
                                       (* -4 (* (* A (* A A)) E))
                                       (+
                                        (* -4 (* (* A (* A A)) C))
                                        (+
                                         (* 2 (* A (* A (* A A))))
                                         (+
                                          (* E E)
                                          (+
                                           (* -2 (* D E))
                                           (+
                                            (* D D)
                                            (+
                                             D
                                             (*
                                              7
                                              C))))))))))))))))))))))
        0))) 
 :UNSAT ) 

;;;
;;; Problem 4 in Redlog format
;;;
 
#|

 phi0 := (((2 * ((C * C) * (E * E))) + ((3 * ((B * B) * (C * C))) + (((0 - 6) * ((B * (B * B)) * C)) + ((3 * (B * (B * (B * B)))) + (((0 - 4) * (A * (C * (E * E)))) + (((0 - 4) * (A * ((C * C) * E))) + (((0 - 6) * (A * (B * (C * C)))) + ((12 * (A * ((B * B) * C))) + (((0 - 6) * (A * (B * (B * B)))) + ((2 * ((A * A) * (E * E))) + ((8 * ((A * A) * (C * E))) + ((6 * ((A * A) * (C * C))) + (((0 - 6) * ((A * A) * (B * C))) + ((3 * ((A * A) * (B * B))) + (((0 - 4) * ((A * (A * A)) * E)) + (((0 - 4) * ((A * (A * A)) * C)) + ((2 * (A * (A * (A * A)))) + ((E * E) + (((0 - 2) * (D * E)) + ((D * D) + (D + (7 * C)))))))))))))))))))))) < 0);
 phi1 := (E = 2) or (E = 1) or (E = 0);
 phi2 := (D <= 1);
 phi3 := (D >= 0);
 phi4 := (C <= 1);
 phi5 := (C >= 0);
 phi6 := (B <= 1);
 phi7 := (B >= 0);
 phi8 := (A <= 1);
 phi9 := (A >= 0);
 phi := ex({B, A, C, E, D}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8 and phi9); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 5 in RAHD format
;;;

 ( (((= (+ (* X1 X1) (* Y1 Y1)) 4)) ((= (+ (* X2 X2) (* Y2 Y2)) 4))
    ((= (+ (* X3 X3) (* Y3 Y3)) 4)) ((= (+ (* X4 X4) (* Y4 Y4)) 4))
    ((= (+ (* X5 X5) (* Y5 Y5)) 4)) ((= (+ (* X6 X6) (* Y6 Y6)) 4))
    ((= (+ (* X7 X7) (* Y7 Y7)) 4))
    ((= (+ (* (- X1 X2) (- X1 X2)) (* (- Y1 Y2) (- Y1 Y2))) 4))
    ((= (+ (* (- X1 X3) (- X1 X3)) (* (- Y1 Y3) (- Y1 Y3))) 4))
    ((= (+ (* (- X1 X4) (- X1 X4)) (* (- Y1 Y4) (- Y1 Y4))) 4))
    ((= (+ (* (- X1 X5) (- X1 X5)) (* (- Y1 Y5) (- Y1 Y5))) 4))
    ((= (+ (* (- X1 X6) (- X1 X6)) (* (- Y1 Y6) (- Y1 Y6))) 4))
    ((= (+ (* (- X1 X7) (- X1 X7)) (* (- Y1 Y7) (- Y1 Y7))) 4))
    ((= (+ (* (- X2 X3) (- X2 X3)) (* (- Y2 Y3) (- Y2 Y3))) 4))
    ((= (+ (* (- X2 X4) (- X2 X4)) (* (- Y2 Y4) (- Y2 Y4))) 4))
    ((= (+ (* (- X2 X5) (- X2 X5)) (* (- Y2 Y5) (- Y2 Y5))) 4))
    ((= (+ (* (- X2 X6) (- X2 X6)) (* (- Y2 Y6) (- Y2 Y6))) 4))
    ((= (+ (* (- X2 X7) (- X2 X7)) (* (- Y2 Y7) (- Y2 Y7))) 4))
    ((= (+ (* (- X3 X4) (- X3 X4)) (* (- Y3 Y4) (- Y3 Y4))) 4))
    ((= (+ (* (- X3 X5) (- X3 X5)) (* (- Y3 Y5) (- Y3 Y5))) 4))
    ((= (+ (* (- X3 X6) (- X3 X6)) (* (- Y3 Y6) (- Y3 Y6))) 4))
    ((= (+ (* (- X3 X7) (- X3 X7)) (* (- Y3 Y7) (- Y3 Y7))) 4))
    ((= (+ (* (- X4 X5) (- X4 X5)) (* (- Y4 Y5) (- Y4 Y5))) 4))
    ((= (+ (* (- X4 X6) (- X4 X6)) (* (- Y4 Y6) (- Y4 Y6))) 4))
    ((= (+ (* (- X4 X7) (- X4 X7)) (* (- Y4 Y7) (- Y4 Y7))) 4))
    ((= (+ (* (- X5 X6) (- X5 X6)) (* (- Y5 Y6) (- Y5 Y6))) 4))
    ((= (+ (* (- X5 X7) (- X5 X7)) (* (- Y5 Y7) (- Y5 Y7))) 4))
    ((> (+ (* (- X6 X7) (- X6 X7)) (* (- Y6 Y7) (- Y6 Y7))) 4))
    ((NOT (= X6 0)) (NOT (= Y6 0)))) 
 :UNSAT ) 

;;;
;;; Problem 5 in Redlog format
;;;

#|
 
 phi0 := not(Y6 = 0) or not(X6 = 0);
 phi1 := ((((X6 - X7) * (X6 - X7)) + ((Y6 - Y7) * (Y6 - Y7))) > 4);
 phi2 := ((((X5 - X7) * (X5 - X7)) + ((Y5 - Y7) * (Y5 - Y7))) = 4);
 phi3 := ((((X5 - X6) * (X5 - X6)) + ((Y5 - Y6) * (Y5 - Y6))) = 4);
 phi4 := ((((X4 - X7) * (X4 - X7)) + ((Y4 - Y7) * (Y4 - Y7))) = 4);
 phi5 := ((((X4 - X6) * (X4 - X6)) + ((Y4 - Y6) * (Y4 - Y6))) = 4);
 phi6 := ((((X4 - X5) * (X4 - X5)) + ((Y4 - Y5) * (Y4 - Y5))) = 4);
 phi7 := ((((X3 - X7) * (X3 - X7)) + ((Y3 - Y7) * (Y3 - Y7))) = 4);
 phi8 := ((((X3 - X6) * (X3 - X6)) + ((Y3 - Y6) * (Y3 - Y6))) = 4);
 phi9 := ((((X3 - X5) * (X3 - X5)) + ((Y3 - Y5) * (Y3 - Y5))) = 4);
 phi10 := ((((X3 - X4) * (X3 - X4)) + ((Y3 - Y4) * (Y3 - Y4))) = 4);
 phi11 := ((((X2 - X7) * (X2 - X7)) + ((Y2 - Y7) * (Y2 - Y7))) = 4);
 phi12 := ((((X2 - X6) * (X2 - X6)) + ((Y2 - Y6) * (Y2 - Y6))) = 4);
 phi13 := ((((X2 - X5) * (X2 - X5)) + ((Y2 - Y5) * (Y2 - Y5))) = 4);
 phi14 := ((((X2 - X4) * (X2 - X4)) + ((Y2 - Y4) * (Y2 - Y4))) = 4);
 phi15 := ((((X2 - X3) * (X2 - X3)) + ((Y2 - Y3) * (Y2 - Y3))) = 4);
 phi16 := ((((X1 - X7) * (X1 - X7)) + ((Y1 - Y7) * (Y1 - Y7))) = 4);
 phi17 := ((((X1 - X6) * (X1 - X6)) + ((Y1 - Y6) * (Y1 - Y6))) = 4);
 phi18 := ((((X1 - X5) * (X1 - X5)) + ((Y1 - Y5) * (Y1 - Y5))) = 4);
 phi19 := ((((X1 - X4) * (X1 - X4)) + ((Y1 - Y4) * (Y1 - Y4))) = 4);
 phi20 := ((((X1 - X3) * (X1 - X3)) + ((Y1 - Y3) * (Y1 - Y3))) = 4);
 phi21 := ((((X1 - X2) * (X1 - X2)) + ((Y1 - Y2) * (Y1 - Y2))) = 4);
 phi22 := (((X7 * X7) + (Y7 * Y7)) = 4);
 phi23 := (((X6 * X6) + (Y6 * Y6)) = 4);
 phi24 := (((X5 * X5) + (Y5 * Y5)) = 4);
 phi25 := (((X4 * X4) + (Y4 * Y4)) = 4);
 phi26 := (((X3 * X3) + (Y3 * Y3)) = 4);
 phi27 := (((X2 * X2) + (Y2 * Y2)) = 4);
 phi28 := (((X1 * X1) + (Y1 * Y1)) = 4);
 phi := ex({X1, Y1, X2, Y2, X3, Y3, X4, Y4, X5, Y5, Y6, Y7, X7, X6}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8 and phi9 and phi10 and phi11 and phi12 and phi13 and phi14 and phi15 and phi16 and phi17 and phi18 and phi19 and phi20 and phi21 and phi22 and phi23 and phi24 and phi25 and phi26 and phi27 and phi28); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 6 in RAHD format
;;;

 ( (((>= (+ (* X3 12 X7 G1) (* G1 G1 -3 G2)) (* X (+ Y 11))))
    ((= (* X X X Y Y) Z)) ((= (* Z W) A)) ((= A 0)) ((>= X 1))
    ((>= Y X)) ((< W -1)) ((> G (+ 82 G1 G2)))
    ((= (* 5 X Y 9 (+ 1 D)) G))) 
 :UNSAT ) 

;;;
;;; Problem 6 in Redlog format
;;;

#|
 
 phi0 := ((5 * (X * (Y * (9 * (1 + D))))) = G);
 phi1 := (G > (82 + (G1 + G2)));
 phi2 := (W < (0 - 1));
 phi3 := (Y >= X);
 phi4 := (X >= 1);
 phi5 := (A = 0);
 phi6 := ((Z * W) = A);
 phi7 := ((X * (X * (X * (Y * Y)))) = Z);
 phi8 := (((X3 * (12 * (X7 * G1))) + (G1 * (G1 * ((0 - 3) * G2)))) >= (X * (Y + 11)));
 phi := ex({X7, X3, Z, A, W, G1, G2, G, X, D, Y}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 7 in RAHD format
;;;

 ( (((= (+ (* X X) (* Y Y) 1) 0))
    ((= (+ (* X2 X2) (* Y2 Y2)) (+ (* X X) (* Y Y) 1)))
    ((= (+ (* X3 X4) (* Y3 Y4)) (+ (* X2 X2) (* Y2 Y2))))
    ((= (+ (* X3 X4) (* Y3 Y4)) (+ (* X X) (* Y Y) 2)))) 
 :UNSAT ) 

;;;
;;; Problem 7 in Redlog format
;;; 

#|

 phi0 := (((X3 * X4) + (Y3 * Y4)) = ((X * X) + ((Y * Y) + 2)));
 phi1 := (((X3 * X4) + (Y3 * Y4)) = ((X2 * X2) + (Y2 * Y2)));
 phi2 := (((X2 * X2) + (Y2 * Y2)) = ((X * X) + ((Y * Y) + 1)));
 phi3 := (((X * X) + ((Y * Y) + 1)) = 0);
 phi := ex({Y2, X2, X, Y, Y3, Y4, X4, X3}, phi0 and phi1 and phi2 and phi3); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 8 in RAHD format
;;;

 ( (((= (* X X X X X X X X X X X X X X X X X X X X X X X X X X X X X X
           X X)
        1))
    ((>= (* Y Y Y) 1000)) ((>= X (+ 1 W))) ((>= W (* Z Z Z)))
    ((>= V (* 3 M M M M M))) ((>= M (* 17 K))) ((>= Z (+ 5 K)))
    ((> (* K K K) 5)) ((= (* Z Z Z) 27))) 
 :UNSAT ) 

;;;
;;; Problem 8 in Redlog format
;;;

#|
 
 phi0 := ((Z * (Z * Z)) = 27);
 phi1 := ((K * (K * K)) > 5);
 phi2 := (Z >= (5 + K));
 phi3 := (M >= (17 * K));
 phi4 := (V >= (3 * (M * (M * (M * (M * M))))));
 phi5 := (W >= (Z * (Z * Z)));
 phi6 := (X >= (1 + W));
 phi7 := ((Y * (Y * Y)) >= 1000);
 phi8 := ((X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * X))))))))))))))))))))))))))))))) = 1);
 phi := ex({Y, X, W, V, M, K, Z}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 9 in RAHD format
;;;

 ( (((= (* X X X X X X X X X X X X X X X X) 1)) ((>= Y 2))
    ((>= X (+ 1 W))) ((>= W (* Z Z Z))) ((>= V (* 3 M M M M M)))
    ((>= M (* 17 K))) ((>= Z (+ 5 K))) ((> (* K K K) 5))
    ((= (* Z Z Z) 27)) ((< W 2) (> W 2))) 
 :UNSAT ) 

;;;
;;; Problem 9 in Redlog format
;;;
 
#|

 phi0 := (W > 2) or (W < 2);
 phi1 := ((Z * (Z * Z)) = 27);
 phi2 := ((K * (K * K)) > 5);
 phi3 := (Z >= (5 + K));
 phi4 := (M >= (17 * K));
 phi5 := (V >= (3 * (M * (M * (M * (M * M))))));
 phi6 := (W >= (Z * (Z * Z)));
 phi7 := (X >= (1 + W));
 phi8 := (Y >= 2);
 phi9 := ((X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * X))))))))))))))) = 1);
 phi := ex({Y, X, V, M, K, Z, W}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8 and phi9); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 10 in RAHD format
;;;

 ( (((>= A 0)) ((>= B 0)) ((>= C 0)) ((>= D 0)) ((>= E 0)) ((>= F 0))
    ((>= G 0)) ((<= A 1)) ((<= B 1)) ((<= C 1)) ((<= D 1)) ((<= E 1))
    ((<= F 1)) ((<= G 1)) ((= (+ (* E E E F F F) G -2) 0))
    ((= (+ (* F F F F) G) (+ G 1)))
    ((= (+ (* 2 G G G G G) (* F F G) (- 0 G)) 0))
    ((< (* (+ F G) (+ F G)
           (+ (* (- 1 (* A A B B)) (- 1 (* C D)) (- (* A D) (* B C))
                 (- (* A D) (* B C)))
              (* (* 2 A B) (- (* C D) (* A B)) (- 1 (* A B)) (- C D)
                 (- C D))
              (* (- (* A A B B) (* C C D D)) (- 1 (* C D)) (- A B)
                 (- A B))))
        0)
     (= (* (+ 2 F G) (+ G 11)) A))) 
 :UNSAT )

;;;
;;; Problem 10 in Redlog format
;;;

#|

 phi0 := (((2 + (F + G)) * (G + 11)) = A) or (((F + G) * ((F + G) * (((1 - (A * (A * (B * B)))) * ((1 - (C * D)) * (((A * D) - (B * C)) * ((A * D) - (B * C))))) + (((2 * (A * B)) * (((C * D) - (A * B)) * ((1 - (A * B)) * ((C - D) * (C - D))))) + (((A * (A * (B * B))) - (C * (C * (D * D)))) * ((1 - (C * D)) * ((A - B) * (A - B)))))))) < 0);
 phi1 := (((2 * (G * (G * (G * (G * G))))) + ((F * (F * G)) + (0 - G))) = 0);
 phi2 := (((F * (F * (F * F))) + G) = (G + 1));
 phi3 := (((E * (E * (E * (F * (F * F))))) + (G + (0 - 2))) = 0);
 phi4 := (G <= 1);
 phi5 := (F <= 1);
 phi6 := (E <= 1);
 phi7 := (D <= 1);
 phi8 := (C <= 1);
 phi9 := (B <= 1);
 phi10 := (A <= 1);
 phi11 := (G >= 0);
 phi12 := (F >= 0);
 phi13 := (E >= 0);
 phi14 := (D >= 0);
 phi15 := (C >= 0);
 phi16 := (B >= 0);
 phi17 := (A >= 0);
 phi := ex({E, F, G, B, C, D, A}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8 and phi9 and phi10 and phi11 and phi12 and phi13 and phi14 and phi15 and phi16 and phi17); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 11 in RAHD format
;;;

 ( (((> (/ X PA) Y)) ((> (/ Y PB) PC)) ((> (* PA PC) R)) ((> PA 0))
    ((> PB 0)) ((> PC 0)) ((NOT (> X (* PB R))))) 
 :UNSAT ) 

;;;
;;; Problem 11 in Redlog format
;;;
 
#|

 phi0 := not(X > (PB * R));
 phi1 := (PC > 0);
 phi2 := (PB > 0);
 phi3 := (PA > 0);
 phi4 := ((PA * PC) > R);
 phi5 := ((Y / PB) > PC);
 phi6 := ((X / PA) > Y);
 phi := ex({Y, PA, PC, X, R, PB}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 12 in RAHD format
;;;

 ( (((NOT (<= (* A C) (* Y X)))) ((= (* X X) C))
    ((= (* Y Y) (+ (* (* A A) C) B))) ((<= 0 B)) ((<= 0 C)) ((<= 0 X))
    ((<= 0 Y))) 
 :UNSAT ) 

;;;
;;; Problem 12 in Redlog format
;;;

#|

 phi0 := (0 <= Y);
 phi1 := (0 <= X);
 phi2 := (0 <= C);
 phi3 := (0 <= B);
 phi4 := ((Y * Y) = (((A * A) * C) + B));
 phi5 := ((X * X) = C);
 phi6 := not((A * C) <= (Y * X));
 phi := ex({A, B, C, X, Y}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 13 in RAHD format
;;;

 ( (((>= A 0)) ((>= B 0)) ((>= C 0)) ((>= D 0)) ((<= A 1)) ((<= B 1))
    ((<= C 1)) ((<= D 1))
    ((< (+ (* (- 1 (* A A B B)) (- 1 (* C D)) (- (* A D) (* B C))
              (- (* A D) (* B C)))
           (* (* 2 A B) (- (* C D) (* A B)) (- 1 (* A B)) (- C D)
              (- C D))
           (* (- (* A A B B) (* C C D D)) (- 1 (* C D)) (- A B)
              (- A B)))
        0))) 
 :UNSAT ) 

;;;
;;; Problem 13 in Redlog format
;;;

#|

 phi0 := ((((1 - (A * (A * (B * B)))) * ((1 - (C * D)) * (((A * D) - (B * C)) * ((A * D) - (B * C))))) + (((2 * (A * B)) * (((C * D) - (A * B)) * ((1 - (A * B)) * ((C - D) * (C - D))))) + (((A * (A * (B * B))) - (C * (C * (D * D)))) * ((1 - (C * D)) * ((A - B) * (A - B)))))) < 0);
 phi1 := (D <= 1);
 phi2 := (C <= 1);
 phi3 := (B <= 1);
 phi4 := (A <= 1);
 phi5 := (D >= 0);
 phi6 := (C >= 0);
 phi7 := (B >= 0);
 phi8 := (A >= 0);
 phi := ex({B, C, D, A}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7 and phi8); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 14 in RAHD format
;;;

 ( (((NOT (< (+ (* X X) (* Y Y)) 1)))
    ((NOT (< (+ (* X X) (* (- Y 1) (- Y 1))) 1)))
    ((NOT (< (+ (* (- X 1) (- X 1)) (* Y Y)) 1)))
    ((NOT (< (+ (* (- X 1) (- X 1)) (* (- Y 1) (- Y 1))) 1)))
    ((<= X 1)) ((<= Y 1)) ((<= 0 X)) ((<= 0 Y))) 
 :UNSAT ) 

;;;
;;; Problem 14 in Redlog format
;;;
 
#|

 phi0 := (0 <= Y);
 phi1 := (0 <= X);
 phi2 := (Y <= 1);
 phi3 := (X <= 1);
 phi4 := not((((X - 1) * (X - 1)) + ((Y - 1) * (Y - 1))) < 1);
 phi5 := not((((X - 1) * (X - 1)) + (Y * Y)) < 1);
 phi6 := not(((X * X) + ((Y - 1) * (Y - 1))) < 1);
 phi7 := not(((X * X) + (Y * Y)) < 1);
 phi := ex({X, Y}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6 and phi7); 

|#




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 15 in RAHD format
;;;

 ( (((= (- (* X (/ YN ZN)) (* R (/ YN ZN))) 0)) ((NOT (= R X)))
    ((NOT (= YN 0))) ((NOT (= ZN 0)))) 
 :UNSAT ) 

;;;
;;; Problem 15 in Redlog format
;;;

#|
 
 phi0 := not(ZN = 0);
 phi1 := not(YN = 0);
 phi2 := not(R = X);
 phi3 := (((X * (YN / ZN)) - (R * (YN / ZN))) = 0);
 phi := ex({R, X, YN, ZN}, phi0 and phi1 and phi2 and phi3); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 16 in RAHD format
;;;

 ( (((NOT (> (+ (* A D) (+ (* C B) (* B D))) 0))) ((>= B 0)) ((>= C 0))
    ((>= D 1)) ((>= (+ (* A A) (- (* A B) (* B B))) 1))
    ((>= (+ (* 2 A) B) 1))
    ((<= (+ (* C C) (+ (- (* C D) (* D D)) 1)) 0))) 
 :UNSAT ) 

;;;
;;; Problem 16 in Redlog format
;;;

#|

 phi0 := (((C * C) + (((C * D) - (D * D)) + 1)) <= 0);
 phi1 := (((2 * A) + B) >= 1);
 phi2 := (((A * A) + ((A * B) - (B * B))) >= 1);
 phi3 := (D >= 1);
 phi4 := (C >= 0);
 phi5 := (B >= 0);
 phi6 := not(((A * D) + ((C * B) + (B * D))) > 0);
 phi := ex({A, B, D, C}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 17 in RAHD format
;;;

 ( (((NOT (>= (- (* A1 A2) (* B1 B2)) 0)))
    ((= (+ (* A1 A1) (* A2 A2)) (+ (* B1 B1) (+ (* B2 B2) 2))))
    ((= (+ (* A1 B1) (* A2 B2)) 0)) ((>= A1 0)) ((>= A2 0))) 
 :UNSAT ) 

;;;
;;; Problem 17 in Redlog format
;;;

#|

 phi0 := (A2 >= 0);
 phi1 := (A1 >= 0);
 phi2 := (((A1 * B1) + (A2 * B2)) = 0);
 phi3 := (((A1 * A1) + (A2 * A2)) = ((B1 * B1) + ((B2 * B2) + 2)));
 phi4 := not(((A1 * A2) - (B1 * B2)) >= 0);
 phi := ex({A2, B2, B1, A1}, phi0 and phi1 and phi2 and phi3 and phi4); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 18 in RAHD format
;;;

 ( (((NOT (>= (+ (* A D) (+ (* C B) (* B D))) 0))) ((>= D 0))
    ((>= (+ (* A A) (- (* A B) (* B B))) 0)) ((>= (+ (* 2 A) B) 0))
    ((<= (+ (* C C) (- (* C D) (* D D))) 0))) 
 :UNSAT ) 

;;;
;;; Problem 18 in Redlog format
;;;
 
#|

 phi0 := (((C * C) + ((C * D) - (D * D))) <= 0);
 phi1 := (((2 * A) + B) >= 0);
 phi2 := (((A * A) + ((A * B) - (B * B))) >= 0);
 phi3 := (D >= 0);
 phi4 := not(((A * D) + ((C * B) + (B * D))) >= 0);
 phi := ex({A, B, D, C}, phi0 and phi1 and phi2 and phi3 and phi4); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 19 in RAHD format
;;;

 ( (((NOT (= X 1))) ((NOT (= Y 1))) ((NOT (= Z 1)))
    ((< (+ (/ (* X X) (* (- X 1) (- X 1)))
           (/ (* Y Y) (* (- Y 1) (- Y 1)))
           (/ (* Z Z) (* (- Z 1) (- Z 1))))
        1))
    ((= (* X Y Z) 1))) 
 :UNSAT ) 

;;;
;;; Problem 19 in Redlog format
;;;

#|
 
 phi0 := ((X * (Y * Z)) = 1);
 phi1 := ((((X * X) / ((X - 1) * (X - 1))) + (((Y * Y) / ((Y - 1) * (Y - 1))) + ((Z * Z) / ((Z - 1) * (Z - 1))))) < 1);
 phi2 := not(Z = 1);
 phi3 := not(Y = 1);
 phi4 := not(X = 1);
 phi := ex({X, Z, Y}, phi0 and phi1 and phi2 and phi3 and phi4); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 20 in RAHD format
;;;

 ( (((NOT (< (- A (* K B)) B))) ((= (* A A) (* (+ (* K K) 1) (* B B))))
    ((<= 1 A)) ((<= 1 B)) ((<= 1 K))) 
 :UNSAT ) 

;;;
;;; Problem 20 in Redlog format
;;;

#|

 phi0 := (1 <= K);
 phi1 := (1 <= B);
 phi2 := (1 <= A);
 phi3 := ((A * A) = (((K * K) + 1) * (B * B)));
 phi4 := not((A - (K * B)) < B);
 phi := ex({A, B, K}, phi0 and phi1 and phi2 and phi3 and phi4); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 21 in RAHD format
;;;

 ( (((NOT (>= (- (* 2 (+ (* X Z) (+ (* X Y) (* Y Z))))
                 (+ (* X X) (+ (* Y Y) (* Z Z))))
              0)))
    ((<= X 125841/50000)) ((<= Y 125841/50000)) ((<= Z 125841/50000))
    ((<= 2 X)) ((<= 2 Y)) ((<= 2 Z))) 
 :UNSAT ) 

;;;
;;; Problem 21 in Redlog format
;;;
 
#|

 phi0 := (2 <= Z);
 phi1 := (2 <= Y);
 phi2 := (2 <= X);
 phi3 := (Z <= 125841/50000);
 phi4 := (Y <= 125841/50000);
 phi5 := (X <= 125841/50000);
 phi6 := not(((2 * ((X * Z) + ((X * Y) + (Y * Z)))) - ((X * X) + ((Y * Y) + (Z * Z)))) >= 0);
 phi := ex({X, Y, Z}, phi0 and phi1 and phi2 and phi3 and phi4 and phi5 and phi6); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 22 in RAHD format
;;;

 ( (((>= (+ (* X X) Y) 0)) ((< Y 0)) ((> (* Y Y) (* X X X X)))) 
 :UNSAT ) 

;;;
;;; Problem 22 in Redlog format
;;;
 
#|

 phi0 := ((Y * Y) > (X * (X * (X * X))));
 phi1 := (Y < 0);
 phi2 := (((X * X) + Y) >= 0);
 phi := ex({X, Y}, phi0 and phi1 and phi2); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem 23 in RAHD format
;;;

 ( (((NOT (= N 0))) ((NOT (= (* (/ 1 N) X) (/ X N))))) 
 :UNSAT ) 

;;;
;;; Problem 23 in Redlog format
;;;
 
#|

 phi0 := not(((1 / N0X) * X) = (X / N0X));
 phi1 := not(N0X = 0);
 phi := ex({X, N0X}, phi0 and phi1); 

|#

;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


))

;;; Good APCAD examples.

; good with interval theatre, bad with tiwari
(wrv 2.5 (apcad-fd-on-case 
	  (mapcar #'car (expand-formula 
			 '(((> C 1)) ((> D 0)) ((< A 1)) ((< B 1))
			   ((< C 2)) ((< D 1))
			   ((< (+ (* (* A A) C) (- A (* B C)))
			       0)) ((> (- C B) C)) ((> B C)))))  
	  #'interval-theatre))

(wrv 2.5 (apcad-fd-on-case (mapcar #'car (expand-formula 
					  '(((> C 1)) ((> D 0)) ((< A 1)) ((< B 1))
					    ((< C 2)) ((< D C))
					    ((< (+ (* (* A A) C) (- A (* B C)))
						0)) ((> (- C B) C)) ((> B C)))))  
			   #'interval-theatre))

; interval theatre does much better than without!
(wrv 2.5 (apcad-fd-on-case (mapcar #'car (expand-formula 
					  '(((< (- (* 2 (+ (* X Z) (+ (* X Y) (* Y Z))))
							 (+ (* X X) (+ (* Y Y) (* Z Z))))
						      0))
					    ((< (* X Z) 12/5))
					    ((< Y 12/5))
					    ((< Z 12/5))
					    ((< 2 X))
					    ((< 2 Y))
					    ((< 2 Z)))))
			   #'interval-theatre))

; interval theatre eliminates one extra sample point at R^2
(wrv 2.5 (apcad-fd-on-case (mapcar #'car (expand-formula
					  '(((NOT (>= (+ (* A D) (+ (* C B) (* B D))) 0)))
					    ((> B 0))
					    ((> C 0))
					    ((> D (- B C)))
					    ((< (+ (* C C) (+ (- (* C D) (* D D)) 1))
						0)))))
					  #'interval-theatre))


; SAT AP-CAD example I walk through in my thesis:

(wrv 2.5 (apcad-fd-on-case (mapcar #'car (expand-formula
					  '(((< (+ (* X1 X4) (+ (* X3 X2) (* X2 X4))) 0))
					    ((> X2 0))
					    ((> X3 0))
					    ((> X4 0))
					    ((< (+ (* X3 X3) (+ (- (* X3 X4) (* X4 X4)) 1))
						0)))))
			   #'interval-theatre :theatre-only? nil :var-order '(X4 X3 X2 X1)))

(wrv 2.5 (apcad-fd-on-case (mapcar #'car (expand-formula

					  '(((NOT (>= (+ (* X (* X (* X X)))
							 (+ (* 2 (* (* X X) Z))
							    (+ (- (* X X) (* 2 (* X (* Y Z))))
							       (+ (* 2 (* (* Y Y) (* Z Z)))
								  (+ (* 2 (* Y (* Z Z)))
								     (+ (- (* 2 (* Z Z)) (* 2 X))
									(+ (* 2 (* Y Z)) 1)))))))
						      0))))))
			   #'interval-theatre))



(wrv 2.5 (apcad-fd-on-case (mapcar #'car (expand-formula
					  '(((< (+ (* A D) (+ (* C B) (* B D))) 0))
					    ((> D 1))
					    ((> (+ (* A A) (- (* A B) (* B B))) 0))
					    ((> (+ (* 2 A) B) (+ B D)))
					    ((> B (* D D)))
					    ((< (+ (* C C) (- (* C D) (* D D))) D)))))
					  
			   #'interval-theatre))

; possibility:

(wrv 3 (fdep-cad-on-case (mapcar #'car (expand-formula
					  '(((< (+ (* A D) (+ (* C B) (* B D))) 0))
					    ((> D 1))
					    ((> (+ (* A A) (- (* A B) (* B B))) 0))
					    ((> (+ (* 2 A) B) (+ B D)))
					    ((> B (* D D)))
					    ((< (+ (* C C) (- (* C D) (* D D))) D))))) :partial? t))


; example from partial CAD paper



(wrv 2.5 (apcad-fd-on-case '((> (* 17/16 T) 6) (< (* 17/16 T) 10) (> (- X (* 17/16 T)) -1)
			     (< (- X (* 17/16 T)) 1) (> (- Y (* 17/16 T)) -9)
			     (< (- Y (* 17/16 T)) -7) (< (+ (* (- X T) (- X T)) (* Y Y)) 1))
					  
			   #'interval-theatre))

(wrv 2.5 (apcad-fd-on-case '((< (+ (+ (* X X) (* Y Y)) (* Z Z)) 1)
			     (< (+ (* X X) (* (- (+ Y Z) 2) (- (+ Y Z) 2))) 1))
			   #'interval-theatre))


(wrv 2.5 (apcad-fd-on-case '((<
                           (+
                            (+
                             (+ (* (* (* A A) (* B B)) (* (- A B) (- A B)))
                                (* (* (* (- A B) (- A B)) (* C (* C C)))
                                   (* D (* D D))))
                             (+
                              (-
                               (* (* (* (* A D) (* A D)) (- 1 (* A B)))
                                  (- (+ 1 (* A B)) (* 2 (* B B))))
                               (* (* (* A D) (* B C))
                                  (+
                                   (+ (- 2 (* (* 4 A) B)) (* B (* A (* A A))))
                                   (* A (* B (* B B))))))
                              (* (* (* (* B C) (* B C)) (- 1 (* A B)))
                                 (- (+ 1 (* A B)) (* 2 (* A A))))))
                            (*
                             (*
                              (+
                               (-
                                (* (* (* (* C C) B) (- 1 (* A B)))
                                   (- (- (* 2 A) B) (* A (* B B))))
                                (* (* C D)
                                   (-
                                    (+ (+ (* A A) (* B B))
                                       (* (* 2 (* A (* A A))) (* B (* B B))))
                                    (* (* 4 (* A A)) (* B B)))))
                               (* (* (* (* D D) A) (- 1 (* A B)))
                                  (- (- (* 2 B) A) (* (* A A) B))))
                              C)
                             D))
                           0)
			     (> A 0) (< A 0) (> B 0) (< B 0) (> C 0) (< C 0)
                          (> D 0) (< D 0)) #'interval-theatre))


;;;
;;;;
;;;;; Walk-through AP-CAD example in thesis:
;;;;
;;;

; Lifting variant I
(wrv 1 (fdep-cad-on-case (mapcar #'car (expand-formula
					  '(((< (+ (* X1 X4) (+ (* X3 X2) (* X2 X4))) 0))
					    ((> X2 0))
					    ((> X3 0))
					    ((> X4 0))
					    ((< (+ (* X3 X3) (+ (- (* X3 X4) (* X4 X4)) 1))
						0)))))
			   :var-order '(X4 X3 X2 X1) :partial? nil))


; Lifting variant II
(wrv 1 (fdep-cad-on-case (mapcar #'car (expand-formula
					  '(((< (+ (* X1 X4) (+ (* X3 X2) (* X2 X4))) 0))
					    ((> X2 0))
					    ((> X3 0))
					    ((> X4 0))
					    ((< (+ (* X3 X3) (+ (- (* X3 X4) (* X4 X4)) 1))
						0)))))
			   :var-order '(X4 X3 X2 X1) :partial? t))



; Lifting variant III
(wrv 1 (apcad-fd-on-case (mapcar #'car (expand-formula
					  '(((< (+ (* X1 X4) (+ (* X3 X2) (* X2 X4))) 0))
					    ((> X2 0))
					    ((> X3 0))
					    ((> X4 0))
					    ((< (+ (* X3 X3) (+ (- (* X3 X4) (* X4 X4)) 1))
						0)))))
			   #'interval-theatre :var-order '(X4 X3 X2 X1) :theatre-only? t))

; Lifting variant IV
(wrv 2.5 (fdep-cad-on-case (mapcar #'car (expand-formula
					  '(((< (+ (* X1 X4) (+ (* X3 X2) (* X2 X4))) 0))
					    ((> X2 0))
					    ((> X3 0))
					    ((> X4 0))
					    ((< (+ (* X3 X3) (+ (- (* X3 X4) (* X4 X4)) 1))
						0)))))
			   :var-order '(X4 X3 X2 X1) :partial? t))


(defun compare-liftings (c)
  (fmt 0 "~%~% Variant I: ~%")
  (wrv 1 (fdep-cad-on-case c :partial? nil))
  (fmt 0 "~%~% Variant II: ~%")
  (wrv 1 (fdep-cad-on-case c :partial? t))
  (fmt 0 "~%~% Variant III: ~%")
  (wrv 1 (apcad-fd-on-case c #'interval-theatre :theatre-only? t))
  (fmt 0 "~%~% Variant IV: ~%")
  (wrv 1 (apcad-fd-on-case c #'interval-theatre :theatre-only? nil)))


(compare-liftings '((< (+ (* A D) (+ (* C B) (* B D))) 0) (> B 0) (> C 0) (> D (- B C))
		    (< (+ (* C C) (+ (- (* C D) (* D D)) 1)) 0)))
 
#|
 Above Gives:
    4 & 2 & 2 & 2
   20 & 5 & 10 & 5
   60 & 3 & 30 & 3
  120 & 6 & 60 & 6
|#

(compare-liftings '((< (- (* 2 (+ (* X Z) (+ (* X Y) (* Y Z)))) (+ (* X X) (+ (* Y Y) (* Z Z))))
    0)
 (< (* X Z) 12/5) (< Y 12/5) (< Z 12/5) (< 2 X) (< 2 Y) (< 2 Z)))

#|
 Above Gives:
   16 & 8 & 0 & 0
   140 & 0 & - & -
   664 & - & - & -
|#


(compare-liftings '((> C 1) (> D 0) (< A 1) (< B 1) (< C 2) (< D 1)
 (< (+ (* (* A A) C) (- A (* B C))) 0) (> (- C B) C) (> B C)))

#|
 Above Gives:
   12  & 10  & 0 & 0
   88  & 19  & - & -
   264 & 19  & - & -
  1320 & 95  & - & -
|#


(compare-liftings '( (< (+ (* A D) (+ (* C B) (* B D))) 0)
		     (> B 0) (> C 0)
		     (> D 1) (> (+ (* A A) (- (* A B) (* B B)) 1))
		     (< (+ (* 2 A) B) 1)
		     (< (+ (* C C) (+ (- (* C D) (* D D)) 1)) 0)))

#|
 Above Gives:
   8   &  3  & 4 & 3
   64  &  8  & 32 & 8
   512 &  8  & 56 & 8
  2560 &  40  & 1280 & 40
|#
