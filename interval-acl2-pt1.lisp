;;;
;;; Verification of RAHD interval calculus within ACL2.
;;; G.O.Passmore, University of Edinburgh
;;;
;;; Began on        1-Sept-2010.
;;; Last updated    2-Sept-2010.
;;;

;;;
;;; (verbose-pstack t)
;;; (dmr-start)
;;; (load "/Research/Programs/TPs/ACL2/acl2-sources/emacs/monitor.el")
;;; (accumulated-persistence t)
;;;

;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::
;;;
;;; Interval endpoints type definition and lemmata.
;;;
;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::

(defund inf? (x)
  (or (equal x '-inf)
      (equal x '+inf)))

(defund is-endpoint? (x)
  (or (rationalp x) (inf? x)))

(defund e-<= (x y)
  (cond ((equal x y) t)
	((and (rationalp x) (rationalp y))
	 (<= x y))
	((or (equal x '-inf) (equal y '+inf)) t)
	(t nil)))
	
(defund e-> (x y)
  (and (not (equal x y))
       (e-<= y x)))

(defund e-< (x y)
  (and (not (equal x y))
       (e-<= x y)))

(defund e->= (x y)
  (e-<= y x))

(defund e-= (x y)
  (and (e-<= x y)
       (e->= x y)))

;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::
;;;
;;; Basic theorems about interval endpoints.
;;;
;;;::::::::::::::::::::::::::::::::::::::::::::::::::::::

(defthm neg-inf-small
  (implies (is-endpoint? e0)
	   (e-<= '-inf e0))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable is-endpoint? e-<= inf?))))

(defthm neg-inf-irrational
  (implies (rationalp e0)
	   (e-< '-inf e0))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable is-endpoint? e-< e-<= inf?))))

(defthm neg-inf-irrational*
  (implies (rationalp e0)
	   (not (e-<= e0 '-inf)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable is-endpoint? e-< e-<= inf?))))

(defthm pos-inf-big
  (implies (is-endpoint? e0)
	   (e-<= e0 '+inf))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable is-endpoint? e-<= inf?))))

(defthm pos-inf-irrational
  (implies (rationalp e0)
	   (e-> '+inf e0))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable is-endpoint? e-> e-<= inf?))))

(defthmd pos-inf-irrational*
  (implies (rationalp e0)
	   (not (e-<= '+inf e0)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable is-endpoint? e-<= inf? e-=))))

(defthmd neg-inf-irrational**
  (implies (rationalp e0)
	   (e-< '-inf e0))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable e-< e-<=))))

(defthmd pos-inf-irrational**
  (implies (rationalp e0)
	   (e-< e0 '+inf))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable e-< e-<=))))

(defthm e-<=-total
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (or (e-<= e0 e1)
	       (e-<= e1 e0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable is-endpoint? e-<= inf?))))

(defthmd e-<=-is-<=-rational
  (implies (and (rationalp e0) (rationalp e1))
	   (iff (e-<= e0 e1)
		(<= e0 e1)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable e-<=))))

(defthmd e-<=-1-0
  (implies (and (rationalp e0)
		(e-<= 1 e0))
	   (not (e-<= e0 0)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable e-<=))))

(defthmd e-=-is-=-rational
  (implies (and (rationalp e0) (rationalp e1))
	   (iff (e-= e0 e1)
		(= e0 e1)))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable e->= e-<= e-= e-<=-is-<=-rational)
	   :use e-<=-is-<=-rational)))

(defthmd e-=-is-equal
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (equal (e-= e0 e1)
		  (equal e0 e1)))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable is-endpoint? e->= e-= e-<= inf? e-=-is-=-rational))))

(defthmd e-=-reflects-=
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (equal (not (e-= e0 e1)) (not (equal e0 e1))))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable is-endpoint? e->= e-= e-<= inf? e-=-is-=-rational))))

(defthm e-<=-anti-symm-l
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (implies (e-<= e0 e1)
		    (equal (e-<= e1 e0) (e-= e0 e1))))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable is-endpoint? e-<= inf? neg-inf-small e-=-is-equal))))

(defthm e-<=-anti-symm-r
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (implies (e-<= e0 e1)
		    (equal (e->= e0 e1) (e-= e0 e1))))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable is-endpoint? e-<= e->= inf? neg-inf-small e-=-is-equal))))

(defthmd e-elim-<
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (equal (e-< e0 e1)
		  (and (e-<= e0 e1) 
		       (not (equal e0 e1)))))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable e-< inf? e->= e-<= e-<=-anti-symm-l e-<=-anti-symm-r is-endpoint? e-<=-is-<=-rational))))

(defthmd e-elim->=
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (equal (e->= e0 e1)
		  (e-<= e1 e0)))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable e-< inf? e->= e-<= e-<=-anti-symm-l e-<=-anti-symm-r is-endpoint? e-<=-is-<=-rational))))

(defthmd e-elim-not-<=
  (implies (and (is-endpoint? e0) (is-endpoint? e1)
		(not (e-<= e0 e1)))
	   (e-<= e1 e0))
  :rule-classes :forward-chaining
  :hints (("Goal" 
	   :in-theory 
	   (enable e-< inf? e->= e-<= is-endpoint? e-<=-is-<=-rational))))

(defthmd e-elim-not->=
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (equal (not (e->= e0 e1))
		  (e-< e0 e1)))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable e-< e-= inf? e->= e-<= is-endpoint? e-<=-is-<=-rational))))

(defthmd e-elim-not->=-rational
  (implies (and (rationalp e0) (rationalp e1))
	   (equal (not (e->= e0 e1))
		  (< e0 e1)))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable e-< inf? e->= e-<= is-endpoint? e-<=-is-<=-rational))))

(defthmd e-elim-not-<=-rational*
  (implies (and (rationalp e0) (rationalp e1) (not (e-<= e0 e1)))
	   (<= e1 e0))
  :rule-classes :forward-chaining
  :hints (("Goal" 
	   :in-theory 
	   (enable e-< inf? e->= e-<= is-endpoint? e-<=-is-<=-rational))))

(defthmd e-<-implies-<=
  (implies (and (is-endpoint? e0) (is-endpoint? e1) (e-< e0 e1))
	   (e-<= e0 e1))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable e-< e-<=))))

(defthmd e-elim->
  (implies (and (is-endpoint? e0) (is-endpoint? e1))
	   (equal (e-> e0 e1)
		  (not (e-<= e0 e1))))
  :rule-classes :rewrite
  :hints (("Goal" 
	   :in-theory 
	   (enable e-> inf? e->= e-= e-<= is-endpoint? e-<=-is-<=-rational))))

(defthmd not-inf-rational
  (implies (is-endpoint? e)
	   (equal (not (inf? e)) (rationalp e)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable is-endpoint? inf?))))

(defthmd not-inf-rational*
  (implies (and (is-endpoint? e) (not (inf? e))) 
	   (rationalp e))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable is-endpoint? inf?))))
  
(defthmd is-endpoint--inf
  (is-endpoint? '-inf)
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-endpoint? inf?))))

(defthmd is-endpoint-+inf
  (is-endpoint? '+inf)
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-endpoint? inf?))))

(defthmd rational-is-endpoint
  (implies (rationalp e)
	   (is-endpoint? e))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable is-endpoint?))))
  

(deftheory e-<=-theory
  '(neg-inf-small pos-inf-big neg-inf-irrational pos-inf-irrational
		  neg-inf-irrational* pos-inf-irrational*
		  e-<=-is-<=-rational e-=-is-=-rational e-=-is-equal 
		  e-<=-anti-symm-l e-<=-anti-symm-r e-< e-> e-<=-1-0
		  e-elim-< e-elim-> e-elim->= neg-inf-irrational** pos-inf-irrational**
		  e-elim-not->=-rational e-elim-not->= e-<-implies-<=
		  e-elim-not-<=-rational* e-=-reflects-= e-elim-not-<=
		  not-inf-rational))

(deftheory e-<=-theory-2
  '(neg-inf-small pos-inf-big neg-inf-irrational pos-inf-irrational
		  neg-inf-irrational* pos-inf-irrational*
		  e-<=-is-<=-rational e-=-is-=-rational e-=-is-equal 
		  e-<=-anti-symm-l e-<=-anti-symm-r e-< e-> e-<=-1-0
		  e-elim-< e-elim-> e-elim->= neg-inf-irrational** pos-inf-irrational**
		  e-elim-not->=-rational e-elim-not->= e-<-implies-<=
		  e-elim-not-<=-rational* e-=-reflects-= e-elim-not-<=
		  not-inf-rational
		  is-endpoint--inf
		  is-endpoint-+inf
		  rational-is-endpoint))

(deftheory e-<=-theory-3
  '(neg-inf-small pos-inf-big neg-inf-irrational pos-inf-irrational
		  neg-inf-irrational* pos-inf-irrational*
		  e-<=-is-<=-rational e-=-is-=-rational e-=-is-equal 
		  e-<=-anti-symm-l e-<=-anti-symm-r e-< e-> e-<=-1-0
		  e-elim-< e-elim-> e-elim->= neg-inf-irrational** pos-inf-irrational**
		  e-elim-not->=-rational e-elim-not->= e-<-implies-<=
		  e-elim-not-<=-rational* e-=-reflects-= e-elim-not-<=
		  not-inf-rational
		  is-endpoint--inf
		  is-endpoint-+inf
		  rational-is-endpoint
		  not-inf-rational*))
