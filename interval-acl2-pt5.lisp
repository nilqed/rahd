;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::
;;;
;;; Emptiness and Realisation.
;;;
;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::

;;;
;;; I-EMPTY?: Is an interval empty?
;;;

(defund i-empty? (i)
  (or (equal i *empty*)
      (let ((i-bt (i-boundary-type i))
	    (i-lb (i-lb i)) (i-ub (i-ub i)))

	;;
	;; There are two reasons an interval will be empty:
	;; 
	;; (a) i=[x,y] with
	;;                  (x>y) \/ (x=+inf) \/ (y=-inf),
	;;
	;; (b) i=[x,y[ or i=]x,y] or i=]x,y[ with
	;;                 (x>=y) \/ (x=+inf) \/ (y=-inf).
	;;

    (case i-bt
	  (0 (or (e-> i-lb i-ub)
		 (equal i-lb '+inf)
		 (equal i-ub '-inf)))
	  (otherwise
	   (or (e->= i-lb i-ub)
	       (equal i-lb '+inf)
	       (equal i-ub '-inf)))))))


;;;
;;; Semantics of our interval realiser, expressed
;;;  in terms of an `is an element of' predicate.
;;;

(defun in-interval? (x i)
  (and (is-interval? i)
       (rationalp x)
       (let ((lb (i-lb i))
	     (ub (i-ub i)))
	 (cond ((and (i-ol? i) (i-or? i))
		; x in ]vlb, vub[
		(and (e-< lb x) (e-< x ub)))
	       ((and (i-cl? i) (i-or? i))
		; x in [vlb, vub[
		(and (e-<= lb x) (e-< x ub)))
	       ((and (i-ol? i) (i-cr? i))
		; x in ]vlb, vub]
		(and (e-< lb x) (e-<= x ub)))
	       ((and (i-cl? i) (i-cr? i))
		; x in [vlb, vub]
		(and (e-<= lb x) (e-<= x ub)))
	       (t nil)))))

;;;
;;; Include a good ACL2 arithmetic book.
;;;

(include-book "arithmetic-3/top" :dir :system)

;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::
;;;
;;; Correctness Theorems for Emptiness and Realisation.
;;;
;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::

;;;
;;; Correctness of emptiness predicate.
;;;

(defthm canonical-empty-is-empty
  (implies (rationalp x)
	   (not (in-interval? x *empty*)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable in-interval? e-<=-theory e-<=-1-0))))

(defthm i-empty-correct
  (implies (and (is-interval? i)
		(i-empty? i))
	   (not (in-interval? x i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty?
				     e-<= e->= e-<=-theory e-<=-1-0 
				     boundary-type-theory))))

(defthmd i-non-empty-rational-bounds-<=
  (implies (and (is-interval? i)
		(not (i-empty? i))
		(and (rationalp (i-lb i)))
		(and (rationalp (i-ub i))))
	   (<= (i-lb i) (i-ub i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? e-<=-theory i-boundary-type e->=))))

;; (defthmd i-non-empty-bounds-<=
;;   (implies (and (is-interval? i)
;; 		(not (i-empty? i)))
;; 	   (e-<= (i-lb i) (i-ub i)))
;;   :hints (("Goal" :in-theory (enable i-empty? e-<=-theory e-<= inf?)
;; 	   :cases ((inf? (i-lb i)) (inf? (i-ub i))))))

(defthmd i-non-empty-endpoints-ok
  (implies (and (is-interval? i)
		(not (i-empty? i)))
	   (and (is-endpoint? (i-lb i))
		(is-endpoint? (i-ub i))))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable i-empty? interval-construction-theory))))

(defthmd i-non-empty--inf-left
  (implies (and (is-interval? i)
		(not (i-empty? i))
		(inf? (i-lb i)))
	   (equal (i-lb i) '-inf))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? interval-construction-theory inf?))))

(defthmd i-non-empty-+inf-right
  (implies (and (is-interval? i)
		(not (i-empty? i))
		(inf? (i-ub i)))
	   (equal (i-ub i) '+inf))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? interval-construction-theory inf?))))

(defthmd i-inhabited-non-empty
  (implies (in-interval? x i)
	   (not (i-empty? i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? i-non-empty--inf-left i-non-empty-+inf-right e-< e-<=
				     i-boundary-type e-> e->=))))

(defthm i-inhabited-continuum
  (implies (and (is-interval? i) (e-< (i-lb i) (i-ub i)))
	   (not (i-empty? i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? e-<=-theory e-< e-<= interval-construction-theory))))

(defthm i-inhabited-continuum*
  (implies (and (is-interval? i) 
		(e-<= (i-lb i) x)
		(not (equal (i-lb i) x))
		(e-<= x (i-ub i))
		(not (equal (i-ub i) x)))
	   (not (i-empty? i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? e-<=-theory e-< e-<= interval-construction-theory))))

(defthm i-inhabited-continuum**
  (implies (and (is-interval? i) 
		(e-<= (i-lb i) x)
		(not (equal (i-lb i) x))
		(e-<= x (i-ub i)))
	   (not (i-empty? i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? e-<=-theory e-< e-<= interval-construction-theory))))

(defthm i-inhabited-closed
  (implies (and (is-interval? i)
		(i-cl? i)
		(i-cr? i)
		(rationalp x)
		(e-<= (i-lb i) x)
		(e-<= x (i-ub i)))
	   (not (i-empty? i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? e-<=-theory e-< e-<= interval-construction-theory
				     i-boundary-type))))

(defthm i-inhabited-clopen
  (implies (and (is-interval? i)
		(i-cl? i)
		(i-or? i)
		(rationalp x)
		(e-<= (i-lb i) x)
		(not (equal x (i-ub i)))
		(e-<= x (i-ub i)))
	   (not (i-empty? i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? e-<=-theory e-< e-<= interval-construction-theory
				     i-boundary-type))))

(defthm i-inhabited-open
  (implies (and (is-interval? i)
		(i-ol? i)
		(i-or? i)
		(rationalp x)
		(e-<= (i-lb i) x)
		(not (equal x (i-ub i)))
		(e-<= x (i-ub i)))
	   (not (i-empty? i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? e-<=-theory e-< e-<= interval-construction-theory
				     i-boundary-type))))

(defthm i-inhabited-closed-left
  (implies (and (i-cl? i)
		(rationalp x)
		(e-<= (i-lb i) x)
		(e-<= x (i-ub i))
		(not (equal x (i-ub i))))
         (not (i-empty? i)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable i-empty? e-<=-theory e-< e-<= interval-construction-theory
				     i-boundary-type i-cl? e->=))))


(deftheory i-emptiness-theory
  '(canonical-empty-is-empty i-empty-correct i-non-empty-rational-bounds-<=
			     i-non-empty-endpoints-ok i-non-empty--inf-left
			     i-non-empty-+inf-right))


(deftheory i-emptiness-theory-2
  '(canonical-empty-is-empty i-empty-correct i-non-empty-rational-bounds-<=
			     i-non-empty-endpoints-ok i-non-empty--inf-left
			     i-non-empty-+inf-right
			     i-inhabited-non-empty
			     i-inhabited-continuum
			     i-inhabited-continuum*
			     i-inhabited-continuum**
			     i-inhabited-closed
			     i-inhabited-clopen
			     i-inhabited-open))

(deftheory i-emptiness-theory-3
  '(canonical-empty-is-empty i-empty-correct i-non-empty-rational-bounds-<=
			     i-non-empty-endpoints-ok i-non-empty--inf-left
			     i-non-empty-+inf-right
			     i-inhabited-non-empty
			     i-inhabited-continuum
			     i-inhabited-continuum*
			     i-inhabited-continuum**
			     i-inhabited-closed
			     i-inhabited-clopen
			     i-inhabited-open
			     i-inhabited-closed-left))

