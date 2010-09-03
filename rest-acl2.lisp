
;;;
;;; I--: Subtract two general intervals.
;;;

(defun i-- (i0 i1)
  (if (or (i-empty? i0)
	  (i-empty? i1))
      *empty*
    (i-op-cond$
     ((or i0-empty? i1-empty?) 'empty)
     (t (make-interval
	 (i-cl-sel (and i0-cl? i1-cr?))
	 (let ((q0 (e-- i0-lb i1-ub)))
	   (if (inf? q0) '-inf q0))
	 (let ((q1 (e-- i0-ub i1-lb)))
	   (if (inf? q1) '+inf q1))
	 (i-cr-sel (and i0-cr? i1-cl?)))))))

(defthmd full-line
  (implies (rationalp x) 
	   (in-interval? x '(] -inf +inf [)))
  :hints (("Goal" :in-theory 
	   (enable e-elim-< e-elim-> e-elim->= 
		   neg-inf-irrational** pos-inf-irrational**))))

;;
;; Let's prove that the realiser for addition is OK.
;;

(defthm i-+-type-preserving
  (implies (and (is-interval? i0) (is-interval? i1))
	   (is-interval? (i-+ i0 i1)))
  :hints (("Goal" :in-theory
	   (enable i-+ i-cr-sel i-cl-sel))))

(defthm i-+-correct
  (implies (and (in-intervalp x i0) (in-intervalp y i1))
	   (in-intervalp (+ x y) (i-+ i0 i1))))
	   
(defthm i---type-preserving
  (implies (and (i-type x) (i-type y))
	   (i-type (i-- x y))))

(defthm i---correct
  (implies (and (in-intervalp x i0) (in-intervalp y i1))
	   (in-intervalp (- x y) (i-- i0 i1))))

;;;
;;; SORT-BCS: Sort boundary candidates.
;;;
;;; As ACL2 is first-order, and to avoid reasoning about an instantiated
;;;  sorting algorithm using e-<, we are just inlining the sorting code
;;;  here to make the ordering explicit and easy to reason about.
;;;
;;; * We can do this as we always know BCS has length 4.
;;;
;;; Cases:
;;;
;;; ((bc0 bc1 bc2 bc3) (bc0 bc1 bc3 bc2) (bc0 bc2 bc1 bc3) (bc0 bc2 bc3 bc1) 
;;;  (bc0 bc3 bc1 bc2) (bc0 bc3 bc2 bc1) (bc1 bc0 bc2 bc3) (bc1 bc0 bc3 bc2) 
;;;  (bc1 bc2 bc0 bc3) (bc1 bc2 bc3 bc0) (bc1 bc3 bc0 bc2) (bc1 bc3 bc2 bc0) 
;;;  (bc2 bc0 bc1 bc3) (bc2 bc0 bc3 bc1) (bc2 bc1 bc0 bc3) (bc2 bc1 bc3 bc0) 
;;;  (bc2 bc3 bc0 bc1) (bc2 bc3 bc1 bc0) (bc3 bc0 bc1 bc2) (bc3 bc0 bc2 bc1) 
;;;  (bc3 bc1 bc0 bc2) (bc3 bc1 bc2 bc0) (bc3 bc2 bc0 bc1) (bc3 bc2 bc1 bc0))
;;;
;;; (defun gen-case (c)
;;;   `((and (bc-<= ,(nth 0 c) ,(nth 1 c))
;;; 	 (bc-<= ,(nth 1 c) ,(nth 2 c))
;;; 	 (bc-<= ,(nth 2 c) ,(nth 3 c)))
;;;     (list ,(nth 0 c) ,(nth 1 c) ,(nth 2 c) ,(nth 3 c))))
;;;
;;; (defun gen-cases (cs)
;;;   (cond ((endp cs) nil)
;;; 	(t (cons (gen-case (car cs))
;;; 		 (gen-cases (cdr cs))))))
;;;
;;; (gen-cases '((bc0 bc1 bc2 bc3) (bc0 bc1 bc3 bc2) (bc0 bc2 bc1 bc3) (bc0 bc2 bc3 bc1) 
;;; 	         (bc0 bc3 bc1 bc2) (bc0 bc3 bc2 bc1) (bc1 bc0 bc2 bc3) (bc1 bc0 bc3 bc2) 
;;; 	         (bc1 bc2 bc0 bc3) (bc1 bc2 bc3 bc0) (bc1 bc3 bc0 bc2) (bc1 bc3 bc2 bc0) 
;;; 	         (bc2 bc0 bc1 bc3) (bc2 bc0 bc3 bc1) (bc2 bc1 bc0 bc3) (bc2 bc1 bc3 bc0) 
;;; 	         (bc2 bc3 bc0 bc1) (bc2 bc3 bc1 bc0) (bc3 bc0 bc1 bc2) (bc3 bc0 bc2 bc1) 
;;; 	         (bc3 bc1 bc0 bc2) (bc3 bc1 bc2 bc0) (bc3 bc2 bc0 bc1) (bc3 bc2 bc1 bc0))).
;;;

(defun bc-<= (bc0 bc1)
  (e-<= (car bc0) (car bc1)))

(defun sort-bcs (bcs)
  (let ((bc0 (car bcs))
	(bc1 (cadr bcs))
	(bc2 (caddr bcs))
	(bc3 (cadddr bcs)))
    (cond ((and (bc-<= bc0 bc1)
		(bc-<= bc1 bc2)
		(bc-<= bc2 bc3))
	   (list bc0 bc1 bc2 bc3))
	  ((and (bc-<= bc0 bc1)
		(bc-<= bc1 bc3)
		(bc-<= bc3 bc2))
	   (list bc0 bc1 bc3 bc2))
	  ((and (bc-<= bc0 bc2)
		(bc-<= bc2 bc1)
		(bc-<= bc1 bc3))
	   (list bc0 bc2 bc1 bc3))
	  ((and (bc-<= bc0 bc2)
		(bc-<= bc2 bc3)
		(bc-<= bc3 bc1))
	   (list bc0 bc2 bc3 bc1))
	  ((and (bc-<= bc0 bc3)
		(bc-<= bc3 bc1)
		(bc-<= bc1 bc2))
	   (list bc0 bc3 bc1 bc2))
	  ((and (bc-<= bc0 bc3)
		(bc-<= bc3 bc2)
		(bc-<= bc2 bc1))
	   (list bc0 bc3 bc2 bc1))
	  ((and (bc-<= bc1 bc0)
		(bc-<= bc0 bc2)
		(bc-<= bc2 bc3))
	   (list bc1 bc0 bc2 bc3))
	  ((and (bc-<= bc1 bc0)
		(bc-<= bc0 bc3)
		(bc-<= bc3 bc2))
	   (list bc1 bc0 bc3 bc2))
	  ((and (bc-<= bc1 bc2)
		(bc-<= bc2 bc0)
		(bc-<= bc0 bc3))
	   (list bc1 bc2 bc0 bc3))
	  ((and (bc-<= bc1 bc2)
		(bc-<= bc2 bc3)
		(bc-<= bc3 bc0))
	   (list bc1 bc2 bc3 bc0))
	  ((and (bc-<= bc1 bc3)
		(bc-<= bc3 bc0)
		(bc-<= bc0 bc2))
	   (list bc1 bc3 bc0 bc2))
	  ((and (bc-<= bc1 bc3)
		(bc-<= bc3 bc2)
		(bc-<= bc2 bc0))
	   (list bc1 bc3 bc2 bc0))
	  ((and (bc-<= bc2 bc0)
		(bc-<= bc0 bc1)
		(bc-<= bc1 bc3))
	   (list bc2 bc0 bc1 bc3))
	  ((and (bc-<= bc2 bc0)
		(bc-<= bc0 bc3)
		(bc-<= bc3 bc1))
	   (list bc2 bc0 bc3 bc1))
	  ((and (bc-<= bc2 bc1)
		(bc-<= bc1 bc0)
		(bc-<= bc0 bc3))
	   (list bc2 bc1 bc0 bc3))
	  ((and (bc-<= bc2 bc1)
		(bc-<= bc1 bc3)
		(bc-<= bc3 bc0))
	   (list bc2 bc1 bc3 bc0))
	  ((and (bc-<= bc2 bc3)
		(bc-<= bc3 bc0)
		(bc-<= bc0 bc1))
	   (list bc2 bc3 bc0 bc1))
	  ((and (bc-<= bc2 bc3)
		(bc-<= bc3 bc1)
		(bc-<= bc1 bc0))
	   (list bc2 bc3 bc1 bc0))
	  ((and (bc-<= bc3 bc0)
		(bc-<= bc0 bc1)
		(bc-<= bc1 bc2))
	   (list bc3 bc0 bc1 bc2))
	  ((and (bc-<= bc3 bc0)
		(bc-<= bc0 bc2)
		(bc-<= bc2 bc1))
	   (list bc3 bc0 bc2 bc1))
	  ((and (bc-<= bc3 bc1)
		(bc-<= bc1 bc0)
		(bc-<= bc0 bc2))
	   (list bc3 bc1 bc0 bc2))
	  ((and (bc-<= bc3 bc1)
		(bc-<= bc1 bc2)
		(bc-<= bc2 bc0))
	   (list bc3 bc1 bc2 bc0))
	  ((and (bc-<= bc3 bc2)
		(bc-<= bc2 bc0)
		(bc-<= bc0 bc1))
	   (list bc3 bc2 bc0 bc1))
	  ((and (bc-<= bc3 bc2)
		(bc-<= bc2 bc1)
		(bc-<= bc1 bc0))
	   (list bc3 bc2 bc1 bc0)))))

(defun bc-type (bc)
  (and (consp bc)
       (equal (len bc) 2)
       (e-type (car bc))
       (booleanp (cdr bc))))

(defun bcs-lst (bcs)
  (and (consp bcs)
       (equal (len bcs) 4)
       (bc-type (car bcs))
       (bc-type (cadr bcs))
       (bc-type (caddr bcs))
       (bc-type (cadddr bcs))))


(defthm sorted-bcs-type-preservation
  (implies (bcs-lst bcs)
	   (bcs-lst (sort-bcs bcs)))
  :hints (("Goal" :in-theory (enable sort-bcs))))

(defthm sorted-bcs-permutation
  (implies (bcs-lst bcs)
	   (iff (member bc bcs)
		(member bc (sort-bcs bcs))))
  :hints (("Goal" :in-theory (enable sort-bcs))))

(defthm sort-bcs-sorted
  (implies (bcs-lst bcs)
	   (and (e-<= (car (sort-bcs bcs)) (cadr (sort-bcs bcs)))
		(e-<= (cadr (sort-bcs bcs)) (caddr (sort-bcs bcs)))
		(e-<= (caddr (sort-bcs bcs)) (cadddr (sort-bcs bcs)))))
  :hints (("Goal" :in-theory (enable sort-bcs))))

(defthm neg-inf-fst
  (implies (and (bcs-lst bcs)
		(or (equal (caar bcs) '-inf)
		    (equal (cadr bcs) '-inf)
		    (equal (caddr bcs) '-inf)
		    (equal (cadddr bcs) '-inf)))
	   (equal (caar (sort-bcs bcs)) '-inf))
  :hints (("Goal" :in-theory (enable sort-bcs))))

(defthm neg-inf-fst*
  (implies (and (bcs-lst bcs)
		(equal bcs (list x y (cons '-inf z) w)))
	   (equal (caar (sort-bcs bcs)) '-inf))
  :hints (("Goal" :in-theory (enable sort-bcs))))

(defthm pos-inf-last
  (implies (and (bcs-lst bcs)
		(or (equal (caar bcs) '+inf)
		    (equal (cadr bcs) '+inf)
		    (equal (caddr bcs) '+inf)
		    (equal (cadddr bcs) '+inf)))
	   (equal (cadddr (sort-bcs bcs)) '+inf))
  :hints (("Goal" :in-theory (enable sort-bcs))))
  
;;;
;;; MULT-CL?: Should the product of two boundaries result
;;;  in a closed boundary type?
;;;
;;;  This is true iff
;;; 
;;;          [closed(b0-bt) /\  closed(b1-bt)]
;;;       \/ [b0-v = 0      /\  closed(b0-bt)] 
;;;       \/ [b1-v = 0      /\  closed(b1-bt)].
;;;

(defun mult-cl? (b0-v b0-bt b1-v b1-bt)
  (or (and b0-bt b1-bt)
      (and (e-= b0-v 0) b0-bt)
      (and (e-= b1-v 0) b1-bt)))

;;;
;;; I-*-Num: Multiply two numerical intervals.
;;;

(defun i-* (i0 i1)
  (if (or (i-empty? i0) (i-empty? i1))
      'empty
    (i-op-cond$
     (t
   
      ;;
      ;; So, i0 * i1 = <min(lst), max(lst),
      ;;                 where
      ;;                lst = (i0-lb * i1-lb,
      ;;                       i0-lb * i1-ub,
      ;;                       i0-ub * i1-lb,
      ;;                       i0-ub * i1-ub), and
      ;;
      ;; `<' and '>' are determined by the logic below.
      ;;
    
      ;;
      ;; Compute a list of boundary candidates, together
      ;;  with their boundary type (closed=T, open=NIL).
      ;;

      (let ((c0-val (e-* i0-lb i1-lb)) 
	    (c0-cl? (mult-cl? i0-lb i0-cl? i1-lb i1-cl?))
	    (c1-val (e-* i0-lb i1-ub)) 
	    (c1-cl? (mult-cl? i0-lb i0-cl? i1-ub i1-cr?))
	    (c2-val (e-* i0-ub i1-lb)) 
	    (c2-cl? (mult-cl? i0-ub i0-cr? i1-lb i1-cl?))
	    (c3-val (e-* i0-ub i1-ub)) 
	    (c3-cl? (mult-cl? i0-ub i0-cr? i1-ub i1-cr?)))

	(let ((bc-lst
	       (list (cons c0-val c0-cl?)
		     (cons c1-val c1-cl?)
		     (cons c2-val c2-cl?)
		     (cons c3-val c3-cl?))))

	  (let* ((sorted-bc-lst (sort-bcs bc-lst))
		 (lbc (nth 0 sorted-bc-lst))
		 (oth-lbc (nth 1 sorted-bc-lst))
		 (oth-ubc (nth 2 sorted-bc-lst))
		 (ubc (nth 3 sorted-bc-lst)))
	  
	    (let ((lb-val (car lbc))
		  (lb-bt (if (e-= (car lbc) (car oth-lbc))
			     (or (cdr lbc) (cdr oth-lbc))
			   (cdr lbc)))
		  (ub-val (car ubc))
		  (ub-bt (if (e-= (car ubc) (car oth-ubc))
			     (or (cdr ubc) (cdr oth-ubc))
			   (cdr ubc))))

	      (make-interval (i-cl-sel lb-bt)
			     lb-val
			     ub-val
			     (i-cr-sel ub-bt))))))))))

;;;
;;; Let's prove I-* correct.
;;;

(defthm i-*-type-preservation
  (implies (and (i-type x) (i-type y))
	   (i-type (i-* x y))))

;;;
;;; Nonlinear lemmata.
;;;

(in-theory (disable in-intervalp))

(defthmd neg-*-neg-is-pos 
  (implies 
   (and (rationalp x) (rationalp y) 
	(< x 0) (< y 0)) (> (* x y) 0)))

(in-theory (enable neg-*-neg-is-pos))

(defthmd *-mono-pos
  (implies (and (rationalp x) (rationalp y)
		(rationalp z) (rationalp w)
		(> x 0) (> y 0) (> z 0) (> w 0)
		(<= x z) (<= y w) )
	   (<= (* x y) (* z w)))
  :hints (("Goal" :nonlinearp t)))

(defthmd *-mono
  (implies (and (rationalp x) (rationalp y)
		(rationalp z) (rationalp w)
		(>= x 0) (>= y 0) (>= z 0) (>= w 0)
		(<= x z) (<= y w) )
	   (<= (* x y) (* z w)))
  :hints (("Goal" :nonlinearp t)))

(in-theory (disable sort-bcs))

(defthm interval-connected
  (implies (and (in-intervalp x i)
		(in-intervalp y i)
		(rationalp z)
		(<= x z)
		(<= z y))
	   (in-intervalp x i)))

(defthm interval-explicit-empty
  (not (in-intervalp x 'empty))
  :hints (("goal" :in-theory (enable in-intervalp))))

(defthm interval-empty
  (implies (and (i-type i) (i-empty? i))
	   (not (in-intervalp x i))))



(defthm i-*-correct
  (implies (and (in-intervalp x i0) (in-intervalp y i1))
	   (in-intervalp (* x y) (i-* i0 i1)))
  :hints (("Subgoal 97" 
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 95" 
	   :in-theory (enable sort-bcs)
	   :nonlinearp t
	   :cases ((and (< x 0) (< y 0))
		   (and (< x 0) (= y 0))
		   (and (< x 0) (> y 0))
		   (and (= x 0) (< y 0))
		   (and (= x 0) (= y 0))
		   (and (= x 0) (> y 0))
		   (and (> x 0) (< y 0))
		   (and (> x 0) (= y 0))
		   (and (> x 0) (> y 0))))
	  ("Subgoal 93"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 91"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 89"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 88"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t
	   :cases ((and (< x 0) (< y 0))
		   (and (< x 0) (= y 0))
		   (and (< x 0) (> y 0))
		   (and (= x 0) (< y 0))
		   (and (= x 0) (= y 0))
		   (and (= x 0) (> y 0))
		   (and (> x 0) (< y 0))
		   (and (> x 0) (= y 0))
		   (and (> x 0) (> y 0))))
	  ("Subgoal 87"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 85"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 83"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 79"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 77"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t
	   :cases ((and (< x 0) (< y 0))
		   (and (< x 0) (= y 0))
		   (and (< x 0) (> y 0))
		   (and (= x 0) (< y 0))
		   (and (= x 0) (= y 0))
		   (and (= x 0) (> y 0))
		   (and (> x 0) (< y 0))
		   (and (> x 0) (= y 0))
		   (and (> x 0) (> y 0))))
	  ("Subgoal 75"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 73"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 72"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 71"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 69"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 68"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 67"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 65"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 63"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 62"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 61"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t)
	  ("Subgoal 60"
	   :in-theory (enable sort-bcs)
	   :nonlinearp t
	   :cases ((= (cadr i1) 0)))
	  
	  ))



	  ("Subgoal 97.101.96.27.2.600.8" :use neg-inf-fst)
	  ("Subgoal 97.101.96.27.2.600.8.299" :use neg-inf-fst)
	  ("Subgoal 1720.104.16.20.3'" :cases ((e-> x 0) (e-= x 0) (e-< x 0)))
	  ("Goal" :cases ((and (e-> x 0) (e-> y 0) (e-> x y))
			  (and (e-> x 0) (e-> y 0) (e-= x y))
			  (and (e-> x 0) (e-> y 0) (e-< x y))
			  (and (e-> x 0) (e-= y 0) (e-> x y))
			  (and (e-> x 0) (e-= y 0) (e-= x y))
			  (and (e-> x 0) (e-= y 0) (e-< x y))
			  (and (e-> x 0) (e-< y 0) (e-> x y))
			  (and (e-> x 0) (e-< y 0) (e-= x y))
			  (and (e-> x 0) (e-< y 0) (e-< x y))
			  (and (e-= x 0) (e-> y 0) (e-> x y))
			  (and (e-= x 0) (e-> y 0) (e-= x y))
			  (and (e-= x 0) (e-> y 0) (e-< x y))
			  (and (e-= x 0) (e-= y 0) (e-> x y))
			  (and (e-= x 0) (e-= y 0) (e-= x y))
			  (and (e-= x 0) (e-= y 0) (e-< x y))
			  (and (e-= x 0) (e-< y 0) (e-> x y))
			  (and (e-= x 0) (e-< y 0) (e-= x y))
			  (and (e-= x 0) (e-< y 0) (e-< x y))
			  (and (e-< x 0) (e-> y 0) (e-> x y))
			  (and (e-< x 0) (e-> y 0) (e-= x y))
			  (and (e-< x 0) (e-> y 0) (e-< x y))
			  (and (e-< x 0) (e-= y 0) (e-> x y))
			  (and (e-< x 0) (e-= y 0) (e-= x y))
			  (and (e-< x 0) (e-= y 0) (e-< x y))
			  (and (e-< x 0) (e-< y 0) (e-> x y))
			  (and (e-< x 0) (e-< y 0) (e-= x y))
			  (and (e-< x 0) (e-< y 0) (e-< x y))))))


(defthm i-*-correct-part (got!)
  (implies (and (in-intervalp x i0) (in-intervalp y i1)
		(> x 0) (> y 0) (> x y))
	   (in-intervalp (* x y) (i-* i0 i1)))
  :hints (("Goal" :nonlinearp t)))

   :hints (("Goal" :cases ((and (e-< (cadr i1) (caddr i0)) (e-< (cadr i1) 0))
			   (and (e-< (cadr i1) (caddr i0)) (e-= (cadr i1) 0))
			   (and (e-< (cadr i1) (caddr i0)) (e-> (cadr i1) 0))
			   (and (e-= (cadr i1) (caddr i0)) (e-< (cadr i1) 0))
			   (and (e-= (cadr i1) (caddr i0)) (e-= (cadr i1) 0))
			   (and (e-= (cadr i1) (caddr i0)) (e-> (cadr i1) 0))
			   (and (e-> (cadr i1) (caddr i0)) (e-< (cadr i1) 0))
			   (and (e-> (cadr i1) (caddr i0)) (e-= (cadr i1) 0))
			   (and (e-> (cadr i1) (caddr i0)) (e-> (cadr i1) 0))))))

  :hints (("Goal" 

;:cases ((e-< (caddr i0) (cadr i1))
;	(e-= (caddr i0) (cadr i1))
;	(e-> (caddr i0) (cadr i1))))))
;
;	   ;; ((and (e-< (cadr i0) 0) (e-< (caddr i0) 0))
;; 			  (and (e-< (cadr i0) 0) (e-= (caddr i0) 0))
;; 			  (and (e-< (cadr i0) 0) (e-> (caddr i0) 0))
;; 			  (and (e-= (cadr i0) 0) (e-< (caddr i0) 0))
;; 			  (and (e-= (cadr i0) 0) (e-= (caddr i0) 0))
;; 			  (and (e-= (cadr i0) 0) (e-> (caddr i0) 0))			  
;; 			  (and (e-> (cadr i0) 0) (e-< (caddr i0) 0))
;; 			  (and (e-> (cadr i0) 0) (e-= (caddr i0) 0))
;; 			  (and (e-> (cadr i0) 0) (e-> (caddr i0) 0))))))




;;;
;;; Next: Interval intersection!
;;;

;;
;; I-INT-CL?: Should the left boundary of intersected
;;  intervals be closed?
;;

(defun intersect-cl? (x y x-cl? y-cl?)
  (cond ((e-> x y) x-cl?)
	((e-> y x) y-cl?)
	(t (and x-cl? y-cl?))))

;;
;; I-INT-CR?: Should the right boundary of intersected
;;  intervals be closed?
;;

(defun intersect-cr? (x y x-cr? y-cr?)
  (cond ((e-< x y) x-cr?)
	((e-< y x) y-cr?)
	(t (and x-cr? y-cr?))))

;;
;; I-MAX: Given two extended rationals, return the max
;;  of them.
;;

(defun e-max (x y)
  (if (e->= x y) x y))

;;
;; I-MIN: Given two extended rationals, return the min
;;  of them.
;;

(defun e-min (x y)
  (if (e-<= x y) x y))

;;
;; I-INTERSECT: Intersect two intervals.
;;

(defun i-intersect (i0 i1)
  (cond ((or (i-empty? i0) (i-empty? i1)) 'empty)
   (t

    ;;
    ;; We will act initially as if we are intersecting two
    ;;  closed intervals, and afterwards will adjust the
    ;;  boundary types of the resulting intersection.
    ;;
    ;; First, we form [x,y] INT [u,v].
    ;;
    ;; To be non-empty, we need:
    ;;  - [x,y] and [u,v] non-empty,
    ;;  - x <= u <= y   -OR-  u <= x <= v.
    ;;

    (i-op-cond$
     ((and (not (and (e-<= i0-lb i1-lb)
		     (e-<= i1-lb i0-ub)))
	   (not (and (e-<= i1-lb i0-lb)
		     (e-<= i0-lb i1-ub))))
      'empty)
     (t (let ((i-candidate 
	       (make-interval
		(i-cl-sel 
		 (intersect-cl? i0-lb i1-lb i0-cl? i1-cl?))
		(e-max i0-lb i1-lb)
		(e-min i0-ub i1-ub)
		(i-cr-sel 
		 (intersect-cr? i0-ub i1-ub i0-cr? i1-cr?)))))
	  (if (i-empty? i-candidate)
	      'empty
	    i-candidate)))))))

;;;
;;; Let's prove intersection correct.
;;;

(defthm intersect-type-preserving
  (implies (and (i-type i0) (i-type i1))
	   (i-type (i-intersect i0 i1))))

(defthm intersect-correct
  (implies (and (rationalp x) (i-type i0) (i-type i1))
	   (iff (in-intervalp x (i-intersect i0 i1))
		(and (in-intervalp x i0)
		     (in-intervalp x i1)))))