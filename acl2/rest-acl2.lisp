
;;;
;;; Nonlinear lemmata.
;;;

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

;; (defthm neg-inf-fst
;;   (implies (and (is-bcs-lst? bcs)
;; 		(or (equal (bc-e (bcs-lst-first bcs)) '-inf)
;; 		    (equal (bc-e (bcs-lst-second bcs)) '-inf)
;; 		    (equal (bc-e (bcs-lst-third bcs)) '-inf)
;; 		    (equal (bc-e (bcs-lst-fourth bcs)) '-inf)))
;; 	   (equal (bc-e (bcs-lst-first (sort-bcs bcs))) '-inf))
;;   :hints (("Goal" :in-theory (enable sort-bcs-sorted
;; 				     single-bc-theory
;; 				     e-<=-theory-4
;; 				     bc-<=--inf-small
;; 				     bc-<=--inf-small*
;; 				     bc-<=-+inf-big
;; 				     bc-<=-+inf-big*))))
;; 	   :cases ((bc-<= (bc-e (bcs-lst-first bcs)) '-inf)))))

;; (defthm neg-inf-fst*
;;   (implies (and (bcs-lst bcs)
;; 		(equal bcs (list x y (cons '-inf z) w)))
;; 	   (equal (caar (sort-bcs bcs)) '-inf))
;;   :hints (("Goal" :in-theory (enable sort-bcs))))

;; (defthm pos-inf-last
;;   (implies (and (bcs-lst bcs)
;; 		(or (equal (caar bcs) '+inf)
;; 		    (equal (cadr bcs) '+inf)
;; 		    (equal (caddr bcs) '+inf)
;; 		    (equal (cadddr bcs) '+inf)))
;; 	   (equal (cadddr (sort-bcs bcs)) '+inf))
;;   :hints (("Goal" :in-theory (enable sort-bcs))))


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

(defthm i-intersect-correct
  (implies (and (rationalp x) (i-type i0) (i-type i1))
	   (iff (in-intervalp x (i-intersect i0 i1))
		(and (in-intervalp x i0)
		     (in-intervalp x i1)))))