
;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::
;;;
;;; Interval boundary types and construction.
;;;
;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::

;;;
;;; Definitions for boundary type symbols.
;;;

(defund is-bt? (x)
  (or (equal x '[) (equal x '])))

;;;
;;; MAKE-INTERVAL: Given left and right interval symbols L,R (either '[ or ']), and
;;;  lower and upper bounds LB, UB (in Q \union {-inf, +inf})), return a RAHD 
;;;  representation of the interval L LB, UB, R.
;;;

(defund make-interval (l lb ub r)
  (list l lb ub r))

(defconst *empty*
  (make-interval '[ 1 0 ']))

(defund is-interval? (x)
  (and (= (len x) 4)
       (is-bt? (car x))
       (is-endpoint? (cadr x))
       (is-endpoint? (caddr x))
       (is-bt? (cadddr x))))

(defund make-closed-interval (lb ub)
  (make-interval '[ lb ub ']))

(defthmd make-interval-is-interval
  (implies (and (is-bt? l) (is-bt? r)
		(is-endpoint? lb) (is-endpoint? ub))
	   (is-interval? (make-interval l lb ub r)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable is-interval? make-interval))))

(defthmd empty-is-interval
  (is-interval? *empty*)
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable is-interval?))))

(defthmd make-closed-interval-is-interval
  (implies (and (is-endpoint? lb) (is-endpoint? ub))
	   (is-interval? (make-closed-interval lb ub)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable make-interval-is-interval
				     make-closed-interval))))

(defthmd make-interval-rational 
  (implies (and (rationalp x) (rationalp y) 
		(is-bt? l) (is-bt? r)) 
	   (is-interval? (make-interval l x y r)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable make-interval-is-interval is-endpoint?))))

;;;
;;; I-LB: Given a RAHD interval representation, return its lower-bound component.
;;;

(defund i-lb (i)
  (cadr i))

(defthmd i-lb-ep
  (implies (is-interval? i)
	   (is-endpoint? (i-lb i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-lb is-interval?))))

(defthmd i-lb-make-same
  (equal (i-lb (make-interval l lb ub r)) lb)
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-lb make-interval))))

;;;
;;; I-UB: Given a RAHD interval representation, return its upper-bound component.
;;;

(defund i-ub (i)
  (caddr i))

(defthmd i-ub-ep
  (implies (is-interval? i)
	   (is-endpoint? (i-ub i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-ub is-interval?))))

(defthmd i-ub-make-same
  (equal (i-ub (make-interval l lb ub r)) ub)
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-ub make-interval))))


(deftheory interval-construction-theory
  '(make-interval-is-interval empty-is-interval make-closed-interval-is-interval
			      i-lb-ep i-ub-ep is-bt?))

(deftheory interval-construction-theory-2
  '(make-interval-is-interval empty-is-interval make-closed-interval-is-interval
			      i-lb-ep i-ub-ep is-bt?
			      i-lb-make-same
			      i-ub-make-same
			      make-interval-rational))
