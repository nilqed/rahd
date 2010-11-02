;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Begin e-* e-<= bound proofs.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; Bound 1: (e-* x-lb y-lb) is smallest.
;;

(set-non-linearp t)

(in-theory (enable *-pos-monotone-lower-bound
		   nla-facts-theory))

(defthmd e-*-e-<=-x-y-bound-split-rational-1
  (implies (and (rationalp x) (rationalp y)
		(rationalp x-lb) (rationalp x-ub)
		(rationalp y-lb) (rationalp y-ub)
		(e-<= x-lb x) (e-<= x x-ub)
		(e-<= y-lb y) (e-<= y y-ub)
		(e-<= (e-* x-lb y-lb) (e-* x-lb y-ub))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-lb))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-ub)))
	   (e-<= (e-* x-lb y-lb) (e-* x y)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" 
	   :in-theory
	   (enable e-<= e-* e-<=-theory-4
		   nla-facts-theory
		   *-pos-monotone-lower-bound
		   force-rational-by-rational-containment
		   e-*-0-is-0
		   e-*-commutative)
	   :cases ((< y-lb 0) (= y-lb 0) (> y-lb 0))
	   )
	  ("Subgoal 3" 
	   :cases ((= y 0) (> y 0)))))

(defthmd e-*-e-<=-x-y-bound-split-irrational-1
  (implies (and (rationalp x) (rationalp y)
		(is-endpoint? x-lb) (is-endpoint? x-ub)
		(is-endpoint? y-lb) (is-endpoint? y-ub)
		(not (and (rationalp x-lb)
			  (rationalp x-ub)
			  (rationalp y-lb)
			  (rationalp y-ub)))
		(e-<= x-lb x) (e-<= x x-ub)
		(e-<= y-lb y) (e-<= y y-ub)
		(e-<= (e-* x-lb y-lb) (e-* x-lb y-ub))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-lb))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-ub)))
	   (e-<= (e-* x-lb y-lb) (* x y)))
  :rule-classes (:rewrite)
  :hints (("Goal" 
	   :cases ((inf? x-lb) (inf? x-ub)
		   (inf? y-lb) (inf? y-ub))
	   :in-theory
	   (enable e-* e-<=-theory-4
		   inf?
		   big-bound-theory
		   big-bound-theory-2)
	   :nonlinearp t)
	  ("Subgoal 3" :in-theory
	   (enable e-* e-<=-theory-4
		   inf? big-bound-theory
		   big-bound-theory-2)
	   :nonlinearp t)
	  ("Subgoal 3.95"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.28"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.27"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.29"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.26''"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.25"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 2" :in-theory
	   (enable e-* e-<=-theory-4
		   inf? big-bound-theory
		   big-bound-theory-2)
	   :nonlinearp t)
	  ("Subgoal 1" :in-theory
	   (enable e-* e-<=-theory-4
		   inf? big-bound-theory
		   big-bound-theory-2)
	   :nonlinearp t)
	  ("Subgoal 1.25"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 1.23"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 1.22"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)))

(defthmd e-*-e-<=-x-y-bound-split-unconditional-1
  (implies (and (rationalp x) (rationalp y)
		(is-endpoint? x-lb) (is-endpoint? x-ub)
		(is-endpoint? y-lb) (is-endpoint? y-ub)
		(e-<= x-lb x) (e-<= x x-ub)
		(e-<= y-lb y) (e-<= y y-ub)
		(e-<= (e-* x-lb y-lb) (e-* x-lb y-ub))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-lb))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-ub)))
	   (e-<= (e-* x-lb y-lb) (e-* x y)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory 
	   (union-theories
	    (theory 'minimal-theory)
	    '(e-*-e-<=-x-y-bound-split-rational-1
	      rational-is-endpoint
	      is-endpoint?
	      e-*-rational-is-*
	      inf-irrational)))
	  ("Subgoal 16" :use
	   (:instance e-*-e-<=-x-y-bound-split-rational-1))
	  ("Subgoal 15" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 14" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 13" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 12" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 11" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 10" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 9" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 8" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 7" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 6" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 5" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 4" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 3" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 2" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 1" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ))







;;
;; Bound 2: (e-* x-lb y-ub) is smallest.
;;



(defthmd e-*-e-<=-x-y-bound-split-rational-2
  (implies (and (rationalp x) (rationalp y)
		(rationalp x-lb) (rationalp x-ub)
		(rationalp y-lb) (rationalp y-ub)
		(e-<= x-lb x) (e-<= x x-ub)
		(e-<= y-lb y) (e-<= y y-ub)
		(e-<= (e-* x-lb y-ub) (e-* x-lb y-lb))
		(e-<= (e-* x-lb y-ub) (e-* x-ub y-lb))
		(e-<= (e-* x-lb y-ub) (e-* x-ub y-ub)))
	   (e-<= (e-* x-lb y-ub) (e-* x y)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" 
	   :in-theory
	   	   (enable e-<= e-* e-<=-theory-4
			   *-pos-monotone-lower-bound
			   force-rational-by-rational-containment
			   e-*-0-is-0
			   e-*-commutative)
	   :nonlinearp t)
	  ("Subgoal 7" 
	   :cases ((< y-lb 0) (= y-lb 0) (> y-lb 0))
	   :nonlinearp t)
	  ("Subgoal 3" 
	   :cases ((< x-lb 0) (= x-lb 0) (> x-lb 0)))))

(and (< y-lb 0) (< y-ub 0) (= x-lb 0))
		   (and (< y-lb 0) (= y-ub 0) (= x-lb 0))
		   (and (< y-lb 0) (> y-ub 0) (= x-lb 0))
		   (and (= y-lb 0) (< y-ub 0) (= x-lb 0))
		   (and (= y-lb 0) (= y-ub 0) (= x-lb 0))
		   (and (= y-lb 0) (> y-ub 0) (= x-lb 0))
		   (and (> y-lb 0) (< y-ub 0) (= x-lb 0))
		   (and (> y-lb 0) (= y-ub 0) (= x-lb 0))
		   (and (> y-lb 0) (> y-ub 0)))
	   :nonlinearp t)
	  ("Subgoal 1" :use tricky-forced-<=-rational-bound-1)))


(defthmd e-*-e-<=-x-y-bound-split-irrational-1
  (implies (and (rationalp x) (rationalp y)
		(is-endpoint? x-lb) (is-endpoint? x-ub)
		(is-endpoint? y-lb) (is-endpoint? y-ub)
		(not (and (rationalp x-lb)
			  (rationalp x-ub)
			  (rationalp y-lb)
			  (rationalp y-ub)))
		(e-<= x-lb x) (e-<= x x-ub)
		(e-<= y-lb y) (e-<= y y-ub)
		(e-<= (e-* x-lb y-lb) (e-* x-lb y-ub))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-lb))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-ub)))
	   (e-<= (e-* x-lb y-lb) (* x y)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" 
	   :cases ((inf? x-lb) (inf? x-ub)
		   (inf? y-lb) (inf? y-ub))
	   :in-theory
	   (enable e-* e-<=-theory-4
		   inf?
		   big-bound-theory
		   big-bound-theory-2)
	   :nonlinearp t)
	  ("Subgoal 3" :in-theory
	   (enable e-* e-<=-theory-4
		   inf? big-bound-theory
		   big-bound-theory-2)
	   :nonlinearp t)
	  ("Subgoal 3.95"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.28"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.27"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.29"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.26''"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 3.25"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 2" :in-theory
	   (enable e-* e-<=-theory-4
		   inf? big-bound-theory
		   big-bound-theory-2)
	   :nonlinearp t)
	  ("Subgoal 1" :in-theory
	   (enable e-* e-<=-theory-4
		   inf? big-bound-theory
		   big-bound-theory-2)
	   :nonlinearp t)
	  ("Subgoal 1.25"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 1.23"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)
	  ("Subgoal 1.22"
	   :in-theory (enable e-* e-<=)
	   :nonlinearp t)))

(defthmd e-*-e-<=-x-y-bound-split-unconditional-1
  (implies (and (rationalp x) (rationalp y)
		(is-endpoint? x-lb) (is-endpoint? x-ub)
		(is-endpoint? y-lb) (is-endpoint? y-ub)
		(e-<= x-lb x) (e-<= x x-ub)
		(e-<= y-lb y) (e-<= y y-ub)
		(e-<= (e-* x-lb y-lb) (e-* x-lb y-ub))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-lb))
		(e-<= (e-* x-lb y-lb) (e-* x-ub y-ub)))
	   (e-<= (e-* x-lb y-lb) (e-* x y)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory 
	   (union-theories
	    (theory 'minimal-theory)
	    '(e-*-e-<=-x-y-bound-split-rational-1
	      rational-is-endpoint
	      is-endpoint?
	      e-*-rational-is-*
	      inf-irrational)))
	  ("Subgoal 16" :use
	   (:instance e-*-e-<=-x-y-bound-split-rational-1))
	  ("Subgoal 15" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 14" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 13" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 12" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 11" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 10" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 9" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 8" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 7" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 6" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 5" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 4" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 3" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 2" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ("Subgoal 1" :use
	   (:instance e-*-e-<=-x-y-bound-split-irrational-1))
	  ))








;;;
;;; ***** Final exported theories.
;;;

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

