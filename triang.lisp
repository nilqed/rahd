;;;
;;; RAHD: Real Algebra in High Dimensions v0.5
;;; A feasible decision method for the existential theory of real closed fields.
;;;
;;; Simple ideal triangulation.
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         24-Nov-2009
;;;            last updated on  24-Nov-2009.
;;;

(defun triangulate-eqs (c-eqs)
  (let ((old-vars-table *vars-table*))
    (let ((*vars-table* (all-vars-in-conj c-eqs)))
      