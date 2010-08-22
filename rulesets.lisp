;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Some default RAHD rulesets which are enabled in the waterfall.
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         27-June-2010,
;;;            last updated on  03-July-2010.
;;;

(defrule squeeze-i
     :conclusion ((< X (* K Z)))
     :hypotheses ((< X (* Y Z))
		  (< Y K)
		  (>= Z 0)))

(defrule squeeze-ii
  :conclusion ((> X (* K Z)))
  :hypotheses ((> X (* Y Z))
	       (> Y K)
	       (>= Z 0)))

(defrule squeeze-iii
  :conclusion ((< Y 0))
  :hypotheses ((< (+ X Y) 0)
	       (>= X 0)))

(defrule squeeze-iv
  :conclusion ((> Y 0))
  :hypotheses ((> (+ X Y) 0)
	       (<= X 0)))

(defrule squeeze-v
  :conclusion ((> X 0))
  :hypotheses ((< Y 0)
	       (< (* X Y) 0)))

(defrule squeeze-vi
  :conclusion ((< X 0))
  :hypotheses ((> Y 0)
	       (< (* X Y) 0)))

(defrule squeeze-vii
  :conclusion ((= 0 1))
  :hypotheses ((> X Y)
	       (> Y X)))

(defrule squeeze-viii
  :conclusion ((= 0 1))
  :hypotheses ((> X Y)
	       (< X Y)))

(defrule squeeze-ix
  :conclusion ((= 0 1))
  :hypotheses ((> X (* (* Y Z) W))
	       (< X (* (* Z Y) W))))

(defrule squeeze-x
  :conclusion ((= 0 1))
  :hypotheses ((> X (* (* Y Z) W))
	       (< X (* (* W Z) Y))))

;;;
;;; Our first ruleset: inequality-squeeze.
;;;

(defruleset inequality-squeeze
  :verified? system
  :active? t
  :rules
  (squeeze-i 
   squeeze-ii 
   squeeze-iii
   squeeze-iv
   squeeze-v
   squeeze-vi
   squeeze-vii
   squeeze-viii
   squeeze-ix
   squeeze-x))

;;;
;;; (verify-ruleset 'inequality-squeeze)
;;;


;;;
;;; Rules based around some simple sign deductions.
;;;

(defrule force-sign-i
  :conclusion ((< (* X Z) 0))
  :hypotheses ((= (+ (* X Y) (* Z W)) 0)
	       (> Y 0)
	       (> W 0)
	       (> (* X Y) 0)))

(defrule force-sign-ii
  :conclusion ((< (* X Z) 0))
  :hypotheses ((= (+ (* X Y) (* Z W)) 0)
	       (> Y 0)
	       (> W 0)
	       (< (* X Y) 0)))

(defrule force-sign-iii
  :conclusion ((> (* W Z) 0))
  :hypotheses ((> X 0)
	       (> Y 0)
	       (< (* X Y) (* W Z))))

(defrule force-sign-iv
  :conclusion ((> (* W Z) 0))
  :hypotheses ((> X 0)
	       (> Y 0)
	       (< (+ (* X Y) (* -1 (* W Z))) 0)))

(defrule force-sign-v
  :conclusion ((< (+ (* Y Z) (* X W)) 0))
  :hypotheses ((= (+ (* -1 (* X X)) Y) 0)
	       (< (+ (* X Z) W) 0)
	       (> X 0)))

(defruleset force-sign
  :verified? system
  :active? t
  :rules
  (force-sign-i
   force-sign-ii
   force-sign-iii
   force-sign-iv
   force-sign-v))

;;;
;;; (verify-ruleset 'force-sign)
;;;



