;;;*************************
;;; Interval Multiplication
;;;*************************

;;;
;;; Algebraic theory for boundary candidates.
;;;

(defund bc-e (bc)
  (car bc))

(defund bc-c? (bc)
  (cdr bc))

(defund is-bc? (bc)
  (and (is-endpoint? (bc-e bc))
       (booleanp (bc-c? bc))))

(defthmd bc-is-cons-pair
  (implies (is-bc? bc)
	   (consp bc))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable is-bc? bc-e bc-c?))))

(defund make-bc (e c?)
  (cons e c?))

(defthmd make-bc-is-bc
  (implies (and (is-endpoint? e)
		(booleanp c?))
	   (is-bc? (make-bc e c?)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bc? bc-e bc-c? make-bc))))

(defthmd make-access-e
  (equal (bc-e (make-bc e x))
	 e)
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable make-bc bc-e))))

(defthmd make-access-c?
  (equal (bc-c? (make-bc x c?))
	 c?)
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable make-bc bc-c?))))

(defthmd bc-e-is-ep
  (implies (is-bc? bc)
	   (is-endpoint? (bc-e bc)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bc? bc-e))))

(defthmd bc-c?-is-bool
  (implies (is-bc? bc)
	   (booleanp (bc-c? bc)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bc? bc-c?))))

(defund make-bcs-lst (a b c d)
  (list a b c d))

(defthmd make-bcs-length-4
  (equal (len (make-bcs-lst a b c d)) 4)
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable make-bcs-lst))))

(defund bcs-lst-first (bcs)
  (car bcs))

(defund bcs-lst-second (bcs)
  (cadr bcs))

(defund bcs-lst-third (bcs)
  (caddr bcs))

(defund bcs-lst-fourth (bcs)
  (cadddr bcs))

(defthmd make-bcs-access-first
  (equal (bcs-lst-first (make-bcs-lst a b c d))
	 a)
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable make-bcs-lst bcs-lst-first))))

(defthmd make-bcs-access-second
  (equal (bcs-lst-second (make-bcs-lst a b c d))
	 b)
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable make-bcs-lst bcs-lst-second))))

(defthmd make-bcs-access-third
  (equal (bcs-lst-third (make-bcs-lst a b c d))
	 c)
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable make-bcs-lst bcs-lst-third))))

(defthmd make-bcs-access-fourth
  (equal (bcs-lst-fourth (make-bcs-lst a b c d))
	 d)
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable make-bcs-lst bcs-lst-fourth))))

(defund is-bcs-lst? (bcs)
  (and (is-bc? (bcs-lst-first bcs))
       (is-bc? (bcs-lst-second bcs))
       (is-bc? (bcs-lst-third bcs))
       (is-bc? (bcs-lst-fourth bcs))
       (equal bcs (make-bcs-lst (bcs-lst-first bcs)
				(bcs-lst-second bcs)
				(bcs-lst-third bcs)
				(bcs-lst-fourth bcs)))))

(defthmd make-bcs-lst-is-bcs-lst
  (implies (and (is-bc? bc0) (is-bc? bc1)
		(is-bc? bc2) (is-bc? bc3))
	   (is-bcs-lst? (make-bcs-lst bc0 bc1 bc2 bc3)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bcs-lst? 
				     make-bcs-access-first
				     make-bcs-access-second
				     make-bcs-access-third
				     make-bcs-access-fourth))))

(defthmd make-bcs-destructor
  (implies (is-bcs-lst? bcs)
	   (equal bcs (make-bcs-lst (bcs-lst-first bcs)
				    (bcs-lst-second bcs)
				    (bcs-lst-third bcs)
				    (bcs-lst-fourth bcs))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable make-bcs-access-first
				     make-bcs-access-second
				     make-bcs-access-third
				     make-bcs-access-fourth
				     is-bcs-lst?))))

(defthmd bcs-lst-access-type-first
  (implies (is-bcs-lst? bcs)
	   (is-bc? (bcs-lst-first bcs)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bcs-lst?))))

(defthmd bcs-lst-access-type-second
  (implies (is-bcs-lst? bcs)
	   (is-bc? (bcs-lst-second bcs)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bcs-lst?))))

(defthmd bcs-lst-access-type-third
  (implies (is-bcs-lst? bcs)
	   (is-bc? (bcs-lst-third bcs)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bcs-lst?))))

(defthmd bcs-lst-access-type-fourth
  (implies (is-bcs-lst? bcs)
	   (is-bc? (bcs-lst-fourth bcs)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bcs-lst?))))

(defund bc-in-bcs (bc bcs)
  (or (equal (bcs-lst-first bcs) bc)
      (equal (bcs-lst-second bcs) bc)
      (equal (bcs-lst-third bcs) bc)
      (equal (bcs-lst-fourth bcs) bc)))

(defthmd bc-first-in-bcs 
  (implies (is-bcs-lst? bcs)
	   (bc-in-bcs (bcs-lst-first bcs) bcs))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-in-bcs))))

(defthmd bc-second-in-bcs 
  (implies (is-bcs-lst? bcs)
	   (bc-in-bcs (bcs-lst-second bcs) bcs))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-in-bcs))))

(defthmd bc-third-in-bcs 
  (implies (is-bcs-lst? bcs)
	   (bc-in-bcs (bcs-lst-third bcs) bcs))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-in-bcs))))

(defthmd bc-fourth-in-bcs 
  (implies (is-bcs-lst? bcs)
	   (bc-in-bcs (bcs-lst-fourth bcs) bcs))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-in-bcs))))

(defund bcs-subset (bcs0 bcs1)
  (and (bc-in-bcs (bcs-lst-first bcs0) bcs1)
       (bc-in-bcs (bcs-lst-second bcs0) bcs1)
       (bc-in-bcs (bcs-lst-third bcs0) bcs1)
       (bc-in-bcs (bcs-lst-fourth bcs0) bcs1)))

(defthmd bcs-subset-self
  (implies (is-bcs-lst? bcs)
	   (bcs-subset bcs bcs))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory 
	   (enable bcs-subset
		   bc-first-in-bcs
		   bc-second-in-bcs
		   bc-third-in-bcs
		   bc-fourth-in-bcs))))

(defthmd bcs-subset-transitive
  (implies (and (bcs-subset bcs0 bcs1)
		(bcs-subset bcs1 bcs2))
	   (bcs-subset bcs0 bcs2))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable bcs-subset bc-in-bcs))))

(defund bcs-permutation (bcs0 bcs1)
  (and (bcs-subset bcs0 bcs1)
       (bcs-subset bcs1 bcs0)))

(defthmd bcs-permutation-commutative
  (equal (bcs-permutation bcs0 bcs1)
	 (bcs-permutation bcs1 bcs0))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bcs-permutation))))

(defthmd bcs-permutation-transitive
  (implies (and (bcs-permutation bcs0 bcs1)
		(bcs-permutation bcs1 bcs2))
	   (bcs-permutation bcs0 bcs2))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory 
	   (enable bcs-permutation bcs-subset-transitive))))

(defthmd bcs-permutation-self
  (implies (is-bcs-lst? bcs)
	   (bcs-permutation bcs bcs))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory
	   (enable bcs-permutation bcs-subset-self))))

(defthmd make-bcs-lst-is-bcs-lst-1
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-first bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-fourth bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-2
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-first bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-third bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-3
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-first bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-fourth bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-4
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-first bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-second bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-5
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-first bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-third bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-6
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-first bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-second bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-7
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-second bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-fourth bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-8
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-second bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-third bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-9
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-second bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-fourth bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-10
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-second bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-first bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-11
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-second bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-third bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-12
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-second bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-first bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-13
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-third bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-fourth bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-14
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-third bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-second bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-15
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-third bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-fourth bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-16
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-third bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-first bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-17
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-third bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-second bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-18
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-third bcs)
                                              (bcs-lst-fourth bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-first bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-19
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-fourth bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-third bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-20
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-fourth bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-second bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-21
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-fourth bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-third bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-22
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-fourth bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-first bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-23
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-fourth bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-first bcs)
                                              (bcs-lst-second bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))
 (defthmd make-bcs-lst-is-bcs-lst-24
          (implies (is-bcs-lst? bcs)
                   (is-bcs-lst? (make-bcs-lst (bcs-lst-fourth bcs)
                                              (bcs-lst-third bcs)
                                              (bcs-lst-second bcs)
                                              (bcs-lst-first bcs))))
          :rule-classes (:rewrite :type-prescription)
          :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst
                                             bcs-lst-access-type-first
                                             bcs-lst-access-type-second
                                             bcs-lst-access-type-third
                                             bcs-lst-access-type-fourth))))

(defthmd make-bcs-lst-perm-1
  (implies (is-bcs-lst? bcs)
	   (bcs-permutation bcs
			    (make-bcs-lst (bcs-lst-first bcs)
					  (bcs-lst-second bcs)
					  (bcs-lst-third bcs)
					  (bcs-lst-fourth bcs))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst 
				     bcs-permutation
				     bcs-subset 
				     make-bcs-access-first
				     make-bcs-access-second
				     make-bcs-access-third
				     make-bcs-access-fourth 
				     bc-in-bcs))))

(defthmd make-bcs-lst-perm-2
  (implies (is-bcs-lst? bcs)
	   (bcs-permutation bcs
			    (make-bcs-lst (bcs-lst-first bcs)
					  (bcs-lst-second bcs)
					  (bcs-lst-fourth bcs)
					  (bcs-lst-third bcs))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst 
				     bcs-permutation
				     bcs-subset 
				     make-bcs-access-first
				     make-bcs-access-second
				     make-bcs-access-third
				     make-bcs-access-fourth 
				     bc-in-bcs))))

(defthmd make-bcs-lst-perm-3
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-first bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-fourth bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst 
				      bcs-permutation
                                      bcs-subset 
				      make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth
				      bc-in-bcs))))

 (defthmd make-bcs-lst-perm-4
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-first bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-second bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst 
				      bcs-permutation
                                      bcs-subset 
				      make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth 
				      bc-in-bcs))))

 (defthmd make-bcs-lst-perm-5
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-first bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-third bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst 
				      bcs-permutation
                                      bcs-subset 
				      make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth 
				      bc-in-bcs))))

 (defthmd make-bcs-lst-perm-6
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-first bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-second bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-7
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-second bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-fourth bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-8
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-second bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-third bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-9
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-second bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-fourth bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-10
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-second bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-first bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-11
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-second bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-third bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-12
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-second bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-first bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-13
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-third bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-fourth bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-14
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-third bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-second bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-15
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-third bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-fourth bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-16
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-third bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-first bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-17
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-third bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-second bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-18
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-third bcs)
                                           (bcs-lst-fourth bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-first bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-19
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-fourth bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-third bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-20
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-fourth bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-second bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-21
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-fourth bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-third bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-22
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-fourth bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-first bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-23
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-fourth bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-first bcs)
                                           (bcs-lst-second bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))

 (defthmd make-bcs-lst-perm-24
   (implies (is-bcs-lst? bcs)
            (bcs-permutation bcs
                             (make-bcs-lst (bcs-lst-fourth bcs)
                                           (bcs-lst-third bcs)
                                           (bcs-lst-second bcs)
                                           (bcs-lst-first bcs))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("goal" :in-theory (enable make-bcs-lst-is-bcs-lst bcs-permutation
                                      bcs-subset make-bcs-access-first
                                      make-bcs-access-second
                                      make-bcs-access-third
                                      make-bcs-access-fourth bc-in-bcs))))



(deftheory single-bc-theory
  '(make-bcs-access-fourth
    make-bcs-access-third
    make-bcs-access-second
    make-bcs-access-first
    bc-c?-is-bool
    bc-e-is-ep
    make-access-c?
    make-access-e
    bc-is-cons-pair
    make-bcs-lst-is-bcs-lst
    bcs-lst-access-type-first
    bcs-lst-access-type-second
    bcs-lst-access-type-third
    bcs-lst-access-type-fourth
    make-bcs-destructor
    bc-first-in-bcs
    bc-second-in-bcs
    bc-third-in-bcs
    bc-fourth-in-bcs
    bcs-subset-transitive
    bcs-subset-self
    bcs-permutation-commutative
    bcs-permutation-transitive
    bcs-permutation-self
    make-bcs-lst-is-bcs-lst-1
    make-bcs-lst-is-bcs-lst-2
    make-bcs-lst-is-bcs-lst-3
    make-bcs-lst-is-bcs-lst-4
    make-bcs-lst-is-bcs-lst-5
    make-bcs-lst-is-bcs-lst-6
    make-bcs-lst-is-bcs-lst-7
    make-bcs-lst-is-bcs-lst-8
    make-bcs-lst-is-bcs-lst-9
    make-bcs-lst-is-bcs-lst-10
    make-bcs-lst-is-bcs-lst-11
    make-bcs-lst-is-bcs-lst-12
    make-bcs-lst-is-bcs-lst-13
    make-bcs-lst-is-bcs-lst-14
    make-bcs-lst-is-bcs-lst-15
    make-bcs-lst-is-bcs-lst-16
    make-bcs-lst-is-bcs-lst-17
    make-bcs-lst-is-bcs-lst-18
    make-bcs-lst-is-bcs-lst-19
    make-bcs-lst-is-bcs-lst-20
    make-bcs-lst-is-bcs-lst-21
    make-bcs-lst-is-bcs-lst-22
    make-bcs-lst-is-bcs-lst-23
    make-bcs-lst-is-bcs-lst-24
    make-bcs-lst-perm-1
    make-bcs-lst-perm-2
    make-bcs-lst-perm-3
    make-bcs-lst-perm-4
    make-bcs-lst-perm-5
    make-bcs-lst-perm-6
    make-bcs-lst-perm-7
    make-bcs-lst-perm-8
    make-bcs-lst-perm-9
    make-bcs-lst-perm-10
    make-bcs-lst-perm-11
    make-bcs-lst-perm-12
    make-bcs-lst-perm-13
    make-bcs-lst-perm-14
    make-bcs-lst-perm-15
    make-bcs-lst-perm-16
    make-bcs-lst-perm-17
    make-bcs-lst-perm-18
    make-bcs-lst-perm-19
    make-bcs-lst-perm-20
    make-bcs-lst-perm-21
    make-bcs-lst-perm-22
    make-bcs-lst-perm-23
    make-bcs-lst-perm-24
    make-bc-is-bc))

(deftheory single-bc-theory-2
  '(make-bcs-lst-is-bcs-lst-1
    make-bcs-lst-is-bcs-lst-2
    make-bcs-lst-is-bcs-lst-3
    make-bcs-lst-is-bcs-lst-4
    make-bcs-lst-is-bcs-lst-5
    make-bcs-lst-is-bcs-lst-6
    make-bcs-lst-is-bcs-lst-7
    make-bcs-lst-is-bcs-lst-8
    make-bcs-lst-is-bcs-lst-9
    make-bcs-lst-is-bcs-lst-10
    make-bcs-lst-is-bcs-lst-11
    make-bcs-lst-is-bcs-lst-12
    make-bcs-lst-is-bcs-lst-13
    make-bcs-lst-is-bcs-lst-14
    make-bcs-lst-is-bcs-lst-15
    make-bcs-lst-is-bcs-lst-16
    make-bcs-lst-is-bcs-lst-17
    make-bcs-lst-is-bcs-lst-18
    make-bcs-lst-is-bcs-lst-19
    make-bcs-lst-is-bcs-lst-20
    make-bcs-lst-is-bcs-lst-21
    make-bcs-lst-is-bcs-lst-22
    make-bcs-lst-is-bcs-lst-23
    make-bcs-lst-is-bcs-lst-24
    make-bcs-lst-perm-1
    make-bcs-lst-perm-2
    make-bcs-lst-perm-3
    make-bcs-lst-perm-4
    make-bcs-lst-perm-5
    make-bcs-lst-perm-6
    make-bcs-lst-perm-7
    make-bcs-lst-perm-8
    make-bcs-lst-perm-9
    make-bcs-lst-perm-10
    make-bcs-lst-perm-11
    make-bcs-lst-perm-12
    make-bcs-lst-perm-13
    make-bcs-lst-perm-14
    make-bcs-lst-perm-15
    make-bcs-lst-perm-16
    make-bcs-lst-perm-17
    make-bcs-lst-perm-18
    make-bcs-lst-perm-19
    make-bcs-lst-perm-20
    make-bcs-lst-perm-21
    make-bcs-lst-perm-22
    make-bcs-lst-perm-23
    make-bcs-lst-perm-24))

(defund bc-<= (bc0 bc1)
  (e-<= (bc-e bc0) (bc-e bc1)))

(defthmd bc-<=-total-1
  (implies (and (is-bc? b0) (is-bc? b1)
		(not (bc-<= b0 b1)))
	   (bc-<= b1 b0))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-<= e-<=-theory is-bc?))))

(defthmd bc-<=-total-2
  (implies (and (is-bc? b0) (is-bc? b1)
		(bc-<= b0 b1)
		(not (equal (bc-e b0) (bc-e b1))))
	   (not (bc-<= b1 b0)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-<= e-<=-theory is-bc?
				     single-bc-theory))))

(defthmd bc-<=-total-3
  (implies (and (is-bc? b0) (is-bc? b1)
		(bc-<= b0 b1)
		(not (bc-<= b1 b0)))
	   (not (equal (bc-e b0) (bc-e b1))))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-<= e-<=-theory is-bc?
				     single-bc-theory))))

(defthmd bc-<=-total-4
  (implies (and (is-bc? b0) (is-bc? b1)
		(bc-<= b0 b1)
		(bc-<= b1 b0))
	   (equal (bc-e b0) (bc-e b1)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-<= e-<=-theory is-bc?
				     single-bc-theory))))

(defthmd bc-<=--inf-small
  (implies (is-bc? bc)
	   (e-<= '-inf (bc-e bc)))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-<= e-<=-theory-4 is-bc?))))

(defthmd bc-<=--inf-small*
  (implies (and (is-bc? bc0) (is-bc? bc1)
		(equal '-inf (bc-e bc0)))
	   (bc-<= bc0 bc1))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-<= bc-<=--inf-small e-<=-theory-4 is-bc?))))

(defthmd bc-<=-+inf-big
  (implies (is-bc? bc)
	   (e-<= (bc-e bc) '+inf))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-<= e-<=-theory-4 is-bc?))))

(defthmd bc-<=-+inf-big*
  (implies (and (is-bc? bc0) (is-bc? bc1)
		(equal (bc-e bc1) '+inf))
	   (bc-<= bc0 bc1))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable bc-<= bc-<=-+inf-big e-<=-theory-4 is-bc?))))

(defthmd bc-<=-anti-symmetric-modulo-c?
  (implies (and (is-bc? b0) (is-bc? b1)
		(bc-<= b0 b1)
		(bc-<= b1 b0))
	   (equal (equal (bc-c? b0) (bc-c? b1))
		  (equal b0 b1)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable bc-<= e-<=-theory is-bc? 
				     single-bc-theory e-<=
				     bc-e bc-c?))))

(defthmd bc-e-is-endpoint
  (implies (is-bc? bc)
	   (is-endpoint? (bc-e bc)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-bc?))))

(defund sort-bcs (bcs)
  (let ((bc0 (bcs-lst-first bcs))
	(bc1 (bcs-lst-second bcs))
	(bc2 (bcs-lst-third bcs))
	(bc3 (bcs-lst-fourth bcs)))
    (cond ((and (bc-<= bc0 bc1)
		(bc-<= bc1 bc2)
		(bc-<= bc2 bc3))
	   (make-bcs-lst bc0 bc1 bc2 bc3))
	  ((and (bc-<= bc0 bc1)
		(bc-<= bc1 bc3)
		(bc-<= bc3 bc2))
	   (make-bcs-lst bc0 bc1 bc3 bc2))
	  ((and (bc-<= bc0 bc2)
		(bc-<= bc2 bc1)
		(bc-<= bc1 bc3))
	   (make-bcs-lst bc0 bc2 bc1 bc3))
	  ((and (bc-<= bc0 bc2)
		(bc-<= bc2 bc3)
		(bc-<= bc3 bc1))
	   (make-bcs-lst bc0 bc2 bc3 bc1))
	  ((and (bc-<= bc0 bc3)
		(bc-<= bc3 bc1)
		(bc-<= bc1 bc2))
	   (make-bcs-lst bc0 bc3 bc1 bc2))
	  ((and (bc-<= bc0 bc3)
		(bc-<= bc3 bc2)
		(bc-<= bc2 bc1))
	   (make-bcs-lst bc0 bc3 bc2 bc1))
	  ((and (bc-<= bc1 bc0)
		(bc-<= bc0 bc2)
		(bc-<= bc2 bc3))
	   (make-bcs-lst bc1 bc0 bc2 bc3))
	  ((and (bc-<= bc1 bc0)
		(bc-<= bc0 bc3)
		(bc-<= bc3 bc2))
	   (make-bcs-lst bc1 bc0 bc3 bc2))
	  ((and (bc-<= bc1 bc2)
		(bc-<= bc2 bc0)
		(bc-<= bc0 bc3))
	   (make-bcs-lst bc1 bc2 bc0 bc3))
	  ((and (bc-<= bc1 bc2)
		(bc-<= bc2 bc3)
		(bc-<= bc3 bc0))
	   (make-bcs-lst bc1 bc2 bc3 bc0))
	  ((and (bc-<= bc1 bc3)
		(bc-<= bc3 bc0)
		(bc-<= bc0 bc2))
	   (make-bcs-lst bc1 bc3 bc0 bc2))
	  ((and (bc-<= bc1 bc3)
		(bc-<= bc3 bc2)
		(bc-<= bc2 bc0))
	   (make-bcs-lst bc1 bc3 bc2 bc0))
	  ((and (bc-<= bc2 bc0)
		(bc-<= bc0 bc1)
		(bc-<= bc1 bc3))
	   (make-bcs-lst bc2 bc0 bc1 bc3))
	  ((and (bc-<= bc2 bc0)
		(bc-<= bc0 bc3)
		(bc-<= bc3 bc1))
	   (make-bcs-lst bc2 bc0 bc3 bc1))
	  ((and (bc-<= bc2 bc1)
		(bc-<= bc1 bc0)
		(bc-<= bc0 bc3))
	   (make-bcs-lst bc2 bc1 bc0 bc3))
	  ((and (bc-<= bc2 bc1)
		(bc-<= bc1 bc3)
		(bc-<= bc3 bc0))
	   (make-bcs-lst bc2 bc1 bc3 bc0))
	  ((and (bc-<= bc2 bc3)
		(bc-<= bc3 bc0)
		(bc-<= bc0 bc1))
	   (make-bcs-lst bc2 bc3 bc0 bc1))
	  ((and (bc-<= bc2 bc3)
		(bc-<= bc3 bc1)
		(bc-<= bc1 bc0))
	   (make-bcs-lst bc2 bc3 bc1 bc0))
	  ((and (bc-<= bc3 bc0)
		(bc-<= bc0 bc1)
		(bc-<= bc1 bc2))
	   (make-bcs-lst bc3 bc0 bc1 bc2))
	  ((and (bc-<= bc3 bc0)
		(bc-<= bc0 bc2)
		(bc-<= bc2 bc1))
	   (make-bcs-lst bc3 bc0 bc2 bc1))
	  ((and (bc-<= bc3 bc1)
		(bc-<= bc1 bc0)
		(bc-<= bc0 bc2))
	   (make-bcs-lst bc3 bc1 bc0 bc2))
	  ((and (bc-<= bc3 bc1)
		(bc-<= bc1 bc2)
		(bc-<= bc2 bc0))
	   (make-bcs-lst bc3 bc1 bc2 bc0))
	  ((and (bc-<= bc3 bc2)
		(bc-<= bc2 bc0)
		(bc-<= bc0 bc1))
	   (make-bcs-lst bc3 bc2 bc0 bc1))
	  ((and (bc-<= bc3 bc2)
		(bc-<= bc2 bc1)
		(bc-<= bc1 bc0))
	   (make-bcs-lst bc3 bc2 bc1 bc0))

	  ;;
	  ;; Dummy unreachable case for easy type-checking.
	  ;;

	  (t (make-bcs-lst bc0 bc1 bc2 bc3)))))

(defthmd sorted-bcs-type-preservation
  (implies (is-bcs-lst? bcs)
	   (is-bcs-lst? (sort-bcs bcs)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory 
	   (enable single-bc-theory sort-bcs bc-<=-total-1))))

(defthm sorted-bcs-permutation
  (implies (is-bcs-lst? bcs)
	   (bcs-permutation bcs (sort-bcs bcs)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory
	   (enable single-bc-theory single-bc-theory-2 sort-bcs
		   bc-<=-anti-symmetric-modulo-c?
		   sorted-bcs-type-preservation))))

(defthm sort-bcs-sorted
  (implies (is-bcs-lst? bcs)
	   (and (bc-<= (bcs-lst-first (sort-bcs bcs)) (bcs-lst-second (sort-bcs bcs)))
		(bc-<= (bcs-lst-second (sort-bcs bcs)) (bcs-lst-third (sort-bcs bcs)))
		(bc-<= (bcs-lst-third (sort-bcs bcs)) (bcs-lst-fourth (sort-bcs bcs)))))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory
	   (enable single-bc-theory single-bc-theory-2 sort-bcs
		   bc-<=-anti-symmetric-modulo-c?
		   bc-<=-total-1 bc-<=-total-2
		   bc-<=-total-3 bc-<=-total-4
		   sorted-bcs-type-preservation))))

(defthm sort-bcs-sorted-on-e-<=
  (implies (is-bcs-lst? bcs)
	   (and (e-<= (bc-e (bcs-lst-first (sort-bcs bcs))) (bc-e (bcs-lst-second (sort-bcs bcs))))
		(e-<= (bc-e (bcs-lst-second (sort-bcs bcs))) (bc-e (bcs-lst-third (sort-bcs bcs))))
		(e-<= (bc-e (bcs-lst-third (sort-bcs bcs))) (bc-e (bcs-lst-fourth (sort-bcs bcs))))))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory
	   (enable single-bc-theory single-bc-theory-2
		   bc-<=-anti-symmetric-modulo-c?
		   bc-<=-total-1 bc-<=-total-2
		   bc-<=-total-3 bc-<=-total-4
		   sorted-bcs-type-preservation
		   sort-bcs-sorted bc-<=)
	  :use (:instance sort-bcs-sorted (bcs bcs)))))


(deftheory sorted-bcs-theory
  '(bc-<=-total-1
    bc-<=-total-2
    bc-<=-total-3
    bc-<=-total-4
    bc-<=--inf-small
    bc-<=--inf-small*
    bc-<=-+inf-big
    bc-<=-+inf-big*
    bc-<=-anti-symmetric-modulo-c?
    sorted-bcs-type-preservation
    sorted-bcs-permutation
    sort-bcs-sorted
    sort-bcs-sorted-on-e-<=))


(defund map-sorted-bcs-to-ecs (bcs)
  (let ((sbcs (sort-bcs bcs)))
    (list (bc-e (bcs-lst-first sbcs))
	  (bc-e (bcs-lst-second sbcs))
	  (bc-e (bcs-lst-third sbcs))
	  (bc-e (bcs-lst-fourth sbcs)))))



  
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
      *empty*
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
	       (make-bcs-lst (make-bc c0-val c0-cl?)
			     (make-bc c1-val c1-cl?)
			     (make-bc c2-val c2-cl?)
			     (make-bc c3-val c3-cl?))))

	  (let* ((sorted-bc-lst (sort-bcs bc-lst))
		 (lbc (bcs-lst-first sorted-bc-lst))
		 (oth-lbc (bcs-lst-second sorted-bc-lst))
		 (oth-ubc (bcs-lst-third sorted-bc-lst))
		 (ubc (bcs-lst-fourth sorted-bc-lst)))
	  
	    (let ((lb-val (bc-e lbc))
		  (lb-bt (if (e-= (bc-e lbc) (bc-e oth-lbc))
			     (or (bc-c? lbc) (bc-c? oth-lbc))
			   (bc-c? lbc)))
		  (ub-val (bc-e ubc))
		  (ub-bt (if (e-= (bc-e ubc) (bc-e oth-ubc))
			     (or (bc-c? ubc) (bc-c? oth-ubc))
			   (bc-c? ubc))))

	      (make-interval (i-cl-sel lb-bt)
			     lb-val
			     ub-val
			     (i-cr-sel ub-bt))))))))))

;;;
;;; Let's prove I-* correct.
;;;

(defthm i-*-type-preservation
  (implies (and (is-interval? x) (is-interval? y))
	   (is-interval? (i-* x y)))
  :hints (("Goal" :in-theory 
	   (enable i-+ boundary-type-theory-3
		   i-emptiness-theory-2
		   e-+-make-interval
		   e-+-ok-on-same
		   e-ops-type-preservation-theory-4
		   sorted-bcs-theory
		   single-bc-theory
		   make-bc-is-bc
		   is-bcs-lst?)
	   :cases ((and (not (equal (i-lb i0) (i-lb i1)))
			(inf? (i-lb i0)) (inf? (i-lb i1)))
		   (and (not (equal (i-ub i0) (i-ub i1)))
			(inf? (i-ub i0)) (inf? (i-ub i1)))))))

(defthm i-*-correct
  (implies (and (in-interval? x i0) (in-interval? y i1))
	   (in-interval? (* x y) (i-* i0 i1)))
  :hints (("Goal" :in-theory 
	   (enable i-+ boundary-type-theory-3
		   i-emptiness-theory-2
		   e-+-make-interval
		   e-+-ok-on-same
		   e-ops-type-preservation-theory-4
		   sorted-bcs-theory
		   single-bc-theory
		   make-bc-is-bc
		   is-bcs-lst?
		   i-*-type-preservation
		   i-lb-make-same
		   sort-bcs-sorted-on-e-<=
		   negate-inf-thm-derive-+inf)
	   :nonlinearp t
	   :cases ((and (not (equal (i-lb i0) (i-lb i1)))
			(inf? (i-lb i0)) (inf? (i-lb i1)))
		   (and (not (equal (i-ub i0) (i-ub i1)))
			(inf? (i-ub i0)) (inf? (i-ub i1)))))))



(defthm i-*-correct-part (got!)
  (implies (and (in-intervalp x i0) (in-intervalp y i1)
		(> x 0) (> y 0) (> x y))
	   (in-intervalp (* x y) (i-* i0 i1)))
  :hints (("Goal" :nonlinearp t)))
