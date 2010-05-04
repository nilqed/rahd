;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; ** Degree shifting for degree reduction of atomic formulae **
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         06-April-2010,
;;;            last updated on  04-May-2010.
;;;

;;;
;;; Note that the variant of the degree shift given in A.Dolzmann's PhD thesis (p41)
;;;   is actually incorrect in the even(gcd) case.  We correct it below.
;;;
;;; Also, special care must be taken to log our degree shifts for recovering SAT
;;;   witnesses.  This is straight-forward and will be covered in my PhD thesis.
;;;
;;; We exploit the following observation:
;;;   Let Phi := \exists x Phi(\vec{u},x), where Phi is qf.
;;;   Let x^{d_1}, ..., x^{d_k} be the occurrences of x in the monomials of Phi.
;;;   Let d := gcd(d_1, ..., d_k) != 0.
;;;   Let c_i := (d_i)/d.
;;;   Let Phi' be obtained from Phi by replacing each x^{d_i} by x^{c_i}.
;;;   Then,
;;;           \exists x Phi(\vec{u},x)  \iff  \exists x \Phi'(\vec{u},x) 
;;;             when odd(d),
;;;      and                            \iff  \exists x (x >= 0  /\  Phi'(\vec{u},x))
;;;             when even(d).
;;;

;;;
;;; COLLECT-POLYS: Given a RAHD CNF formula, collect all
;;;  polynomials which appear in its atoms.
;;;

(defun collect-polys-cnf (f)
  (let ((out nil))
    (dolist (c f)
      (dolist (l c)
	(let ((x (cadr l))
	      (y (caddr l)))
	  (setq out 
		(union out
		       (list (if (equal y 0)
				 x
			       `(- ,x ,y))))))))
    out))

;;;
;;; GCD-POW-V-IN-POLYS: Given a collection of polynomials polys and
;;;  a variable v, compute the gcd of all appearing powers of v in
;;;  polys.
;;;
;;; Polys are given in algebraic representation.
;;;

(defun gcd-pow-v-in-polys (polys var-id)
  (let ((working-gcd nil))
    (dolist (p polys)
      (dolist (m p)
	(let ((pp (cdr m)))
	  (let ((vp (extract-vp-in-v pp var-id)))
	    (when vp
	      (let ((pow (cdr vp)))
		(if (not working-gcd) (setq working-gcd pow)
		  (setq working-gcd (gcd working-gcd pow)))))))))
    working-gcd))

;;;
;;; DEGSHIFT-V-BY-GCD-POLY: Given a polynomial, a VAR-ID, and a GCD,
;;;  return the result of shifting down each monomial occurrence of
;;;  v by its cofactor w.r.t. GCD.
;;;
;;; Polynomial given and returned in algebraic representation.
;;;

(defun degshift-v-by-gcd-poly (p var-id gcd) 
  (let ((p* (poly-prover-rep-to-alg-rep p)))
    

;;;
;;; DEGSHIFT-V-BY-GCD: Given a RAHD formula, a variable v, and a gcd,
;;;  return the result of modifying every appearance of v in a polynomial
;;;  in the case to its power cofactor w.r.t. gcd.
;;;

(defun degshift-v-by-gcd-f (f var-id gcd-pow)
  (cond ((not (consp f)) f)
	(t (case (car f)
	     ((:AND :OR :IFF :IMPLIES)
	      (list (car f)
		    (degshift-v-by-gcd-f (cadr f))
		    (degshift-v-by-gcd-f (caddr f))))
	     (:NOT (list ':NOT (degshift-v-by-gcd-f (cadr f))))
	     ((> < >= <= =)
	      (list (car f) 
		    (degshift-v-by-gcd-f (cadr f))
		    (degshift-v-by-gcd-f (caddr f))))
	     (t (deg-shift-v-by-gcd-poly f))))))

;;;
;;; Given a collection of polynomials, a variable v, and a formula f,
;;;  return the result of degree shifting down f w.r.t. v.
;;;
  
(defun degshift-polys-f (polys v c)
  (let ((var-id (find-var v *vars-table* 0)))
    (let ((gcd-pow (gcd-pow-v-in-polys polys var-id)))
      (if gcd-pow
	  
	  ;;
	  ;; Now, we have compute the gcd of the powers of every appearance
	  ;;  of v in the list of polynomials.  We can now substitute using
	  ;;  the derived cofactors.
	  ;;
	  
	  (degshift-v-by-gcd-f (gcd-pow var-id f)) 
	f))))