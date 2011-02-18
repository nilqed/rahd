;;;
;;; I-L: Given a RAHD interval representation, return its left boundary symbol.
;;;

(defund i-lbt (i)
  (car i))

(defthmd i-lbt-ep
  (implies (is-interval? i)
	   (is-bt? (i-lbt i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-lbt is-interval? is-bt?))))

;;;
;;; I-R: Given a RAHD interval representation, return its right boundary symbol.
;;;

(defund i-rbt (i)
  (cadddr i))

(defthmd i-rbt-ep
  (implies (is-interval? i)
	   (is-bt? (i-rbt i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-rbt is-interval? is-bt?))))

;;;
;;; I-OL?: Is an interval's left boundary type open?
;;;

(defund i-ol? (i)
  (equal (i-lbt i) ']))

;;;
;;; I-OR?: Is an interval's right boundary type open?
;;;

(defund i-or? (i)
  (equal (i-rbt i) '[))

;;;
;;; I-CL?: Is an interval's left boundary type closed?
;;;

(defund i-cl? (i)
  (not (i-ol? i)))

;;;
;;; I-CR?: Is an interval's right boundary type closed?
;;;

(defund i-cr? (i)
  (not (i-or? i)))

;;;
;;; I-BOUNDARY-TYPE: Given a RAHD interval representation, return n in {0,1,2,3} s.t.
;;;   I-BOUNDARY-TYPE(i) = 0 if i = [x,y] (closed),
;;;                        1 if i = [x,y[ (clopen-oR),
;;;                        2 if i = ]x,y] (clopen-oL),
;;;                        3 if i = ]x,y[ (open).
;;;

(defund i-boundary-type (i)
  (cond ((and (i-cl? i) (i-cr? i)) 0)
	((and (i-cl? i) (i-or? i)) 1)
	((and (i-ol? i) (i-cr? i)) 2)
	((and (i-ol? i) (i-or? i)) 3)))

;;;
;;; I-CL-SEL: If the argument is T, return a closed left
;;;  boundary type (bt).  Otherwise, return an open left bt.
;;;

(defund i-cl-sel (x)
  (if x '[ ']))

;;;
;;; I-CR-SEL: If the argument is T, return a closed right
;;;  boundary type (bt).  Otherwise, return an open right bt.
;;;

(defund i-cr-sel (x)
  (if x '] '[))


(defthmd i-ol-make
  (i-ol? (make-interval '] x y z))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-ol? make-interval i-lbt))))

(defthmd i-or-make
  (i-or? (make-interval x y z '[))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-or? make-interval i-rbt))))

(defthmd i-cl-make
  (i-cl? (make-interval '[ x y z))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-cl? make-interval i-lbt i-ol?))))

(defthmd i-cr-make
  (i-cr? (make-interval x y z ']))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-cr? make-interval i-rbt i-or?))))

(defthmd i-ol-iff
  (implies (is-interval? i)
	   (equal (i-ol? i) (not (i-cl? i))))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-cl? make-interval i-rbt i-ol?))))

(defthmd i-or-iff
  (implies (is-interval? i)
	   (equal (i-or? i) (not (i-cr? i))))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-cr? make-interval i-rbt i-or?))))
  

;;;
;;; Boundary-type theory definition.
;;;

(deftheory boundary-type-theory
  '(i-boundary-type i-cl-sel i-cr-sel i-lb-ep
		    i-ub-ep))

(deftheory boundary-type-theory-2
  '(i-boundary-type i-cl-sel i-cr-sel i-lb-ep
		    i-ub-ep
		    i-ol-make
		    i-or-make
		    i-cl-make
		    i-cr-make))

(deftheory boundary-type-theory-3
  '(i-boundary-type i-cl-sel i-cr-sel i-lb-ep
		    i-ub-ep
		    i-ol-make
		    i-or-make
		    i-cl-make
		    i-cr-make
		    i-ol-iff
		    i-or-iff))