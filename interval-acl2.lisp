;;;
;;; I-OP-COND$: A simple macro for conditionally operating on intervals.
;;;

(defmacro i-op-cond$ (&rest rst)
  `(let ((i0-bt (i-boundary-type i0)) (i1-bt (i-boundary-type i1))
	 (i0-lb (i-lb i0)) (i0-ub (i-ub i0))
	 (i1-lb (i-lb i1)) (i1-ub (i-ub i1))
	 (i0-ol? (i-ol? i0)) (i1-ol? (i-ol? i1))
	 (i0-or? (i-or? i0)) (i1-or? (i-or? i1))
	 (i0-empty? (i-empty? i0))
	 (i1-empty? (i-empty? i1)))
     (declare (ignorable i0-bt i1-bt i0-lb i0-ub i1-lb
			 i1-ub i0-ol? i1-or? i0-ol? i0-or?
			 i0-empty? i1-empty?))
     (let ((i0-cl? (not i0-ol?)) (i1-cl? (not i1-ol?))
	   (i0-cr? (not i0-or?)) (i1-cr? (not i1-or?)))
       (declare (ignorable i0-cl? i0-cr? i1-cl? i1-cr?))
       (cond ,@rst))))


;;;*************************
;;; Interval Addition
;;;*************************

;;;
;;; I-+: Add two general intervals.
;;;

(defun i-+ (i0 i1)
  (if (or (i-empty? i0) 
	  (i-empty? i1))
      *empty*
    (i-op-cond$
     (t (make-interval
	 (i-cl-sel (and i0-cl? i1-cl?))
	 (e-+ i0-lb i1-lb)
	 (e-+ i0-ub i1-ub)
	 (i-cr-sel (and i0-cr? i1-cr?)))))))

(in-theory (enable interval-construction-theory))

(defthmd i-+-type-preservation
  (implies (and (is-interval? i0) (is-interval? i1)
		(not (i-empty? i0))
		(not (i-empty? i1)))
	   (is-interval? (i-+ i0 i1)))
  :hints (("Goal" :in-theory 
	   (enable i-+ boundary-type-theory
		   i-emptiness-theory
		   e-+-make-interval
		   e-+-ok-on-same
		   e-ops-type-preservation-theory)
	   :cases ((and (not (equal (i-lb i0) (i-lb i1)))
			(inf? (i-lb i0)) (inf? (i-lb i1)))
		   (and (not (equal (i-ub i0) (i-ub i1)))
			(inf? (i-ub i0)) (inf? (i-ub i1)))))))

;;
;; Let's prove that the realiser for addition is OK.
;;

(defthm i-+-correct-empty
  (implies (and (in-interval? x i0) (in-interval? y i1)
		(or (i-empty? i0) (i-empty? i1)))
	   (in-interval? (+ x y) (i-+ i0 i1)))
  :hints (("Goal"
	   :in-theory
	   (enable i-emptiness-theory-2 i-+-type-preservation
		   e-<=-theory i-+ interval-construction-theory))))
		       
(in-theory (enable e-+-ok-on-same e-+-make-interval))

(defthm i-+-correct-non-empty
  (implies (and (in-interval? x i0) (in-interval? y i1)
		(not (i-empty? i0)) (not (i-empty? i1)))
	   (in-interval? (+ x y) (i-+ i0 i1)))
  :hints (("Goal"
	   :in-theory
	   (enable i-emptiness-theory-2 
		   e-ops-type-preservation-theory-4
		   e-<=-theory-2 e-+-ok-on-same
		   boundary-type-theory-3
		   interval-construction-theory-2)
	   :cases ((and (not (equal (i-lb i0) (i-lb i1)))
			(inf? (i-lb i0)) (inf? (i-lb i1)))
		   (and (not (equal (i-ub i0) (i-ub i1)))
			(inf? (i-ub i0)) (inf? (i-ub i1)))))
	  ("Subgoal 3" :in-theory 
	   (enable e-<= e-< e-<=-theory-2
		   e-ops-type-preservation-theory-4
		   boundary-type-theory-3
		   interval-construction-theory-2))))

(in-theory (disable e-+-ok-on-same e-+-make-interval i-+))

(defthm i-+-correct
  (implies (and (in-interval? x i0) (in-interval? y i1))
	   (in-interval? (+ x y) (i-+ i0 i1)))
  :hints (("Goal"
	   :in-theory (enable i-+-correct-empty
			      i-+-correct-non-empty)
	   :cases ((i-empty? i0) (i-empty? i1)))))

;; ^^^ Got it!  4:49am on 3-September-2010! Yesss!




;;;*************************
;;; Interval Subtraction
;;;*************************

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

(in-theory (enable i-- in-interval?))

(defthm i---correct
  (implies (and (in-interval? x i0) (in-interval? y i1))
	   (in-interval? (- x y) (i-- i0 i1)))
    :hints (("Goal"
	   :in-theory
	   (enable i-emptiness-theory-2
		   e-ops-type-preservation-theory-5
		   e-<=-theory-3
		   boundary-type-theory-3
		   interval-construction-theory-2)
	   :cases ((and (not (equal (i-lb i0) (i-lb i1)))
			(inf? (i-lb i0)) (inf? (i-lb i1)))
		   (and (not (equal (i-ub i0) (i-ub i1)))
			(inf? (i-ub i0)) (inf? (i-ub i1)))))
	    ("Subgoal 3" :in-theory 
	     (enable e-<= e-< e-<=-theory-2
		     e-ops-type-preservation-theory-5
		     boundary-type-theory-3
		     interval-construction-theory-2
		     is-bt? inf?))
	    ("Subgoal 2" :in-theory
	     (enable e-<= e-< e-<=-theory-2
		  i-emptiness-theory-3
		  e-ops-type-preservation-theory-5
		  boundary-type-theory-3
		  interval-construction-theory-2
		  is-bt? inf?))))


;; ^^^ Got it!  6:40am on 3-September-2010! Yesss!
