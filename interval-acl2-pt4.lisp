;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::
;;;
;;; Arithmetic of interval endpoints.
;;;
;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::

;;;
;;; NEGATE-INF: Given x in {-inf,+inf}, return (-1)*x.
;;;

(defund negate-inf (x)
  (cond ((equal x '-inf) '+inf)
	((equal x '+inf) '-inf)))

(defthmd negate-inf-type-preservation
  (implies (inf? x)
	   (inf? (negate-inf x)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable inf? negate-inf))))

(defthmd negate-inf-op
  (implies (inf? x)
	   (not (e-= (negate-inf x) x)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable inf? negate-inf e-=))))

;;;
;;; E-+: Add two elements of (Q \union {-inf, +inf}).
;;;       Note: -inf + +inf is undefined and causes an error.
;;;

(defund e-+ (x y)
  (cond ((and (rationalp x) (rationalp y))
	 (+ x y))
	((and (rationalp x) (inf? y))
	 y)
	((and (inf? x) (rationalp y))
	 x)
	((and (inf? x) (inf? y) (equal x y))
	 x)))

(defthmd inf-irrational
  (implies (inf? x) (not (rationalp x)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable inf?))))

(defthmd e-+-type-preservation
  (implies (and (is-endpoint? x) (is-endpoint? y)
		(implies (and (inf? x) (inf? y))
			 (equal x y)))
	   (is-endpoint? (e-+ x y)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory
	   (enable e-+ is-endpoint?))))

(defthmd e-+-type-preservation*
  (implies (and (is-endpoint? x) (is-endpoint? y)
		(or (not (inf? x)) (not (inf? y))))
	   (is-endpoint? (e-+ x y)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory
	   (enable e-+-type-preservation))))

(defthmd e-+-type-preservation*-fc
  (implies (and (is-endpoint? x) (is-endpoint? y)
		(or (not (inf? x)) (not (inf? y))))
	   (is-endpoint? (e-+ x y)))
  :rule-classes (:forward-chaining :type-prescription)
  :hints (("Goal" :in-theory
	   (enable e-+-type-preservation))))

(defthmd e-+-bad-case
  (implies (and (is-endpoint? x) (is-endpoint? y))
	   (equal (not (is-endpoint? (e-+ x y)))
		  (and (inf? x) (inf? y)
		       (not (equal x y)))))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory
	   (enable is-endpoint? inf? e-+-type-preservation))))

(in-theory (enable e-+-bad-case))

(defthmd e-+-make-interval-light
  (implies (and (is-bt? l) (is-bt? r)
		(is-endpoint? (e-+ e0 e1))
		(is-endpoint? (e-+ e2 e3)))
	   (is-interval?
	    (make-interval l (e-+ e0 e1) (e-+ e2 e3) r)))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory (enable e-+-type-preservation*-fc
			      make-interval-is-interval))))
(defthmd e-+-ok-on-same
  (implies (is-endpoint? e)
	   (is-endpoint? (e-+ e e)))
  :hints (("Goal" :in-theory (enable e-+-type-preservation))))

(defthmd e-+-ok-on-lb
  (implies (is-interval? i)
	   (is-endpoint? (e-+ (i-lb i) (i-lb i))))
  :hints (("Goal" :in-theory (enable e-+-ok-on-same boundary-type-theory))))
  
(defthmd e-+-ok-on-ub
  (implies (is-interval? i)
	   (is-endpoint? (e-+ (i-ub i) (i-ub i))))
  :hints (("Goal" :in-theory (enable e-+-ok-on-same boundary-type-theory))))

(defthmd e-+-make-interval
  (implies (and (is-bt? l) (is-bt? r)
		(is-endpoint? e0) (is-endpoint? e1)
		(is-endpoint? e2) (is-endpoint? e3)
		(not (and (inf? e0) (inf? e1) (not (equal e0 e1))))
		(not (and (inf? e2) (inf? e3) (not (equal e2 e3)))))
	   (is-interval?
	    (make-interval l (e-+ e0 e1) (e-+ e2 e3) r)))
  :hints (("Goal" 
	   :in-theory (enable e-+-type-preservation*-fc
			      e-+-make-interval-light
			      e-+-bad-case
			      e-+-ok-on-same))))

(defthmd e-+-make-interval-lb
  (implies (and (is-interval? i)
		(is-bt? l) (is-bt? r))
	   (is-interval? (make-interval
			  l
			  (e-+ (i-lb i) (i-lb i))
			  (e-+ (i-lb i) (i-lb i))
			  r)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable e-+-ok-on-same e-+-ok-on-lb boundary-type-theory))))

(defthmd e-+-make-interval-ub
  (implies (and (is-interval? i)
		(is-bt? l) (is-bt? r))
	   (is-interval? (make-interval
			  l
			  (e-+ (i-ub i) (i-ub i))
			  (e-+ (i-ub i) (i-ub i))
			  r)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable e-+-ok-on-same e-+-ok-on-ub boundary-type-theory))))


(defthmd e-+-rational-is-rational
  (implies (and (rationalp e0) (rationalp e1))
	   (rationalp (e-+ e0 e1)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable e-+))))
  
(defthmd e-+-rational-is-+
  (implies (and (rationalp e0) (rationalp e1))
	   (equal (e-+ e0 e1) (+ e0 e1)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e-+))))

(defthmd e-+-inf-is-inf
  (implies (and (rationalp x)
		(inf? y))
	   (equal (e-+ x y) y))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e-+ inf?))))

(defthmd e-+-inf-is-inf*
  (implies (and (rationalp x)
		(inf? y))
	   (equal (e-+ y x) y))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e-+ inf?))))

;;;
;;; E--: Subtract two elements in (Q \union {-inf, +inf}).
;;;       Note: Subtraction of infinities of opposite signs
;;;        is permitted here, as it is caught and handled
;;;        soundly in the context of interval subtraction
;;;        in i---num below.
;;;

(defund e-- (x y)
  (cond ((and (rationalp x) (rationalp y))
	 (- x y))
	((and (rationalp x) (inf? y))
	 (negate-inf y))
	((and (inf? x) (rationalp y))
	 x)
	((not (equal x y))
	 (if (equal x '+inf) '-inf '+inf))))

(defthmd e---type-preservation
  (implies (and (is-endpoint? x) (is-endpoint? y)
		(implies (and (inf? x) (inf? y))
			 (not (equal x y))))
	   (is-endpoint? (e-- x y)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory
	   (enable e-- is-endpoint?
		   negate-inf-type-preservation))))

(defthmd e--rational-is--
  (implies (and (rationalp e0) (rationalp e1))
	   (equal (e-- e0 e1) (- e0 e1)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory
	   (enable e--))))

(defthmd e--rational-is-rational
  (implies (and (rationalp e0) (rationalp e1))
	   (rationalp (e-- e0 e1)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory
	   (enable e--rational-is--))))

(defthmd e--pos->=
  (implies (and (is-endpoint? e0) (is-endpoint? e1)
		(not (and (inf? e0) (inf? e1)))
		(e->= e0 e1))
	   (e->= (e-- e0 e1) 0))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory
	   (enable e-- e-<=-theory-3 e->= e-<=
		   e--rational-is-rational))))

(defthm not-e--inf-both-rational
  (implies (and (is-endpoint? e0) (is-endpoint? e1)
		(is-endpoint? (e-- e0 e1))
		(not (inf? (e-- e0 e1))))
	   (and (rationalp e0)
		(rationalp e1)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory
	   (enable e-- e-<=-theory-3 e->= e-<=))))

(defthmd e---ok-on-same-rational
  (implies (rationalp e)
	   (is-endpoint? (e-- e e)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable e--rational-is--))))

(defthmd e---ok-on-lb-rational
  (implies (and (is-interval? i)
		(rationalp (i-lb i)))
	   (is-endpoint? (e-- (i-lb i) (i-lb i))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable e---ok-on-same-rational boundary-type-theory))))

(defthmd e---ok-on-ub-rational
  (implies (and (is-interval? i)
		(rationalp (i-ub i)))
	   (is-endpoint? (e-- (i-ub i) (i-ub i))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable e---ok-on-same-rational boundary-type-theory))))

(defthmd e---ok-make-interval-same-rational-lb
  (implies (and (rationalp (i-lb i))
		(is-bt? l) (is-bt? r))
	   (is-interval? (make-interval l
					(e-- (i-lb i) (i-lb i))
					(e-- (i-lb i) (i-lb i))
					r)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e--rational-is-- make-interval-is-interval))))

(defthmd e---ok-make-interval-same-rational-ub
  (implies (and (rationalp (i-ub i))
		(is-bt? l) (is-bt? r))
	   (is-interval? (make-interval l
					(e-- (i-ub i) (i-ub i))
					(e-- (i-ub i) (i-ub i))
					r)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e--rational-is-- make-interval-is-interval))))

					
(defthmd irrational-e--inf
  (implies (rationalp (e-- e0 e1))
	   (and (not (inf? e0))
		(not (inf? e1))))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e-- inf?))))

(defthmd irrational-e--inf-not
  (not (rationalp (e-- e0 '-inf)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e-- inf?))))

(defthmd irrational-e--inf-not*
  (not (rationalp (e-- e0 '+inf)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e-- inf?))))

(defthmd irrational-e--inf-not**
  (not (rationalp (e-- '-inf e1)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e-- inf?))))

(defthmd irrational-e--inf-not***
  (not (rationalp (e-- '+inf e1)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e-- inf?))))

(defthmd e---inf-irrational
  (implies (rationalp x)
	   (not (equal x (e-- '+inf y))))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e--))))

(defthmd e---inf-irrational*
  (implies (rationalp x)
	   (not (equal x (e-- '-inf y))))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e--))))

(defthmd e---+inf-rational
  (implies (rationalp e)
	   (equal (e-- '+inf e) '+inf))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e--))))

(defthmd e---+inf-rational*
  (implies (rationalp e)
	   (equal (e-- e '+inf) '-inf))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e--))))

(defthmd e----inf-rational
  (implies (rationalp e)
	   (equal (e-- '-inf e) '-inf))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e--))))

(defthmd e----inf-rational*
  (implies (rationalp e)
	   (equal (e-- e '-inf) '+inf))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable e--))))


;;;
;;; E-*: Multiply two elements in (Q \union {-inf, +inf}.
;;;       Note that this multiplication of +-inf's and 0 is sound
;;;       for its use in interval containment.
;;;

(defund e-* (x y)
  (cond ((and (rationalp x) (rationalp y))
	 (* x y))
	((and (rationalp x) (inf? y))
	 (if (= x 0) 0
	   (if (< x 0) (negate-inf y) 
	     y)))
	((and (inf? x) (rationalp y))
	 (if (= y 0) 0
	   (if (< y 0) (negate-inf x)
	     x)))
	((and (inf? x) (inf? y))
	 (cond ((equal x y)
		'+inf)
	       (t '-inf)))))

(defthmd e-*-type-preservation
  (implies (and (is-endpoint? x) (is-endpoint? y))
	   (is-endpoint? (e-* x y)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory
	   (enable e-* is-endpoint?
		   negate-inf-type-preservation))))

(deftheory e-ops-type-preservation-theory
  '(e-+-type-preservation e---type-preservation e-*-type-preservation
			  e-+-make-interval e-+-ok-on-same))

(deftheory e-ops-type-preservation-theory-2
  '(e-+-type-preservation e---type-preservation e-*-type-preservation
			  e-+-make-interval e-+-ok-on-same
			  e-+-bad-case e-+-make-interval-light
			  e-+-type-preservation*-fc
			  e-+-ok-on-ub
			  e-+-ok-on-lb
			  e-+-make-interval-ub
			  e-+-make-interval-lb))

(deftheory e-ops-type-preservation-theory-3
  '(e-+-type-preservation e---type-preservation e-*-type-preservation
			  e-+-make-interval e-+-ok-on-same
			  e-+-bad-case e-+-make-interval-light
			  e-+-type-preservation*-fc
			  e-+-ok-on-ub
			  e-+-ok-on-lb
			  e-+-make-interval-ub
			  e-+-make-interval-lb
			  e-+-rational-is-rational
			  e-+-rational-is-+))

(deftheory e-ops-type-preservation-theory-4
  '(e-+-type-preservation e---type-preservation e-*-type-preservation
			  e-+-make-interval e-+-ok-on-same
			  e-+-bad-case e-+-make-interval-light
			  e-+-type-preservation*-fc
			  e-+-ok-on-ub
			  e-+-ok-on-lb
			  e-+-make-interval-ub
			  e-+-make-interval-lb
			  e-+-rational-is-rational
			  e-+-rational-is-+
			  e-+-inf-is-inf
			  e-+-inf-is-inf*))

(deftheory e-ops-type-preservation-theory-5
  '(e-+-type-preservation e---type-preservation e-*-type-preservation
			  e-+-make-interval e-+-ok-on-same
			  e-+-bad-case e-+-make-interval-light
			  e-+-type-preservation*-fc
			  e-+-ok-on-ub
			  e-+-ok-on-lb
			  e-+-make-interval-ub
			  e-+-make-interval-lb
			  e-+-rational-is-rational
			  e-+-rational-is-+
			  e-+-inf-is-inf
			  e-+-inf-is-inf*
			  e--rational-is--
			  e--rational-is-rational
			  e--pos->=
			  not-e--inf-both-rational
			  e---ok-on-same-rational
			  e---ok-on-lb-rational
			  e---ok-on-ub-rational
			  e---ok-make-interval-same-rational-lb
			  e---ok-make-interval-same-rational-ub
			  irrational-e--inf
			  irrational-e--inf-not
			  irrational-e--inf-not*
			  irrational-e--inf-not**
			  irrational-e--inf-not***
			  e---inf-irrational
			  e---inf-irrational*
			  e---+inf-rational
			  e---+inf-rational*
			  e----inf-rational
			  e----inf-rational*))

