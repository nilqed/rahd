;;;
;;; RAHD: Real Algebra in High Dimensions v0.0
;;; A feasible decision method for the existential theory of real closed fields.
;;;
;;; ** A parser translating MetiTarski problems to RAHD problems **
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         05-Dec-2008,
;;;            last updated on  05-Dec-2008.
;;;

#|

Example: ? skoX _dot_ skoX = 0 /\\ rational 1 3 <= skoX

'(? skoX _dot_ skoX = 0 /\\ rational 1 3 <= skoX) 

 (? SKOX _DOT_ SKOX = 0 /\\ RATIONAL 1 3 <= SKOX)

|#

;;;
;;; STRIP-QS: Strip the leading quantifier block from M-T formulas.
;;;

(defun strip-qs (f)
  