;;; Compiled by f2cl version:
;;; ("f2cl1.l,v 1.215 2009/04/07 22:05:21 rtoy Exp $"
;;;  "f2cl2.l,v 1.37 2008/02/22 22:19:33 rtoy Exp $"
;;;  "f2cl3.l,v 1.6 2008/02/22 22:19:33 rtoy Exp $"
;;;  "f2cl4.l,v 1.7 2008/02/22 22:19:34 rtoy Exp $"
;;;  "f2cl5.l,v 1.200 2009/01/19 02:38:17 rtoy Exp $"
;;;  "f2cl6.l,v 1.48 2008/08/24 00:56:27 rtoy Exp $"
;;;  "macros.l,v 1.112 2009/01/08 12:57:19 rtoy Exp $")

;;; Using Lisp CMU Common Lisp 19f (19F)
;;; 
;;; Options: ((:prune-labels nil) (:auto-save t) (:relaxed-array-decls t)
;;;           (:coerce-assigns :as-needed) (:array-type ':simple-array)
;;;           (:array-slicing nil) (:declare-common nil)
;;;           (:float-format double-float))

(in-package :slatec)


(let ((zeror 0.0) (zeroi 0.0))
  (declare (type (double-float) zeror zeroi))
  (defun zkscl (zrr zri fnu n yr yi nz rzr rzi ascle tol elim)
    (declare (type (simple-array double-float (*)) yi yr)
             (type (f2cl-lib:integer4) nz n)
             (type (double-float) elim tol ascle rzi rzr fnu zri zrr))
    (prog ((cyr (make-array 2 :element-type 'double-float))
           (cyi (make-array 2 :element-type 'double-float)) (i 0) (ic 0)
           (idum 0) (kk 0) (nn 0) (nw 0) (acs 0.0) (as 0.0) (cki 0.0) (ckr 0.0)
           (csi 0.0) (csr 0.0) (fn 0.0) (str 0.0) (s1i 0.0) (s1r 0.0) (s2i 0.0)
           (s2r 0.0) (zdr 0.0) (zdi 0.0) (celmr 0.0) (elm 0.0) (helim 0.0)
           (alas 0.0))
      (declare (type (simple-array double-float (2)) cyr cyi)
               (type (double-float) alas helim elm celmr zdi zdr s2r s2i s1r
                                    s1i str fn csr csi ckr cki as acs)
               (type (f2cl-lib:integer4) nw nn kk idum ic i))
      (setf nz 0)
      (setf ic 0)
      (setf nn (min (the f2cl-lib:integer4 2) (the f2cl-lib:integer4 n)))
      (f2cl-lib:fdo (i 1 (f2cl-lib:int-add i 1))
                    ((> i nn) nil)
        (tagbody
          (setf s1r (f2cl-lib:fref yr (i) ((1 n))))
          (setf s1i (f2cl-lib:fref yi (i) ((1 n))))
          (setf (f2cl-lib:fref cyr (i) ((1 2))) s1r)
          (setf (f2cl-lib:fref cyi (i) ((1 2))) s1i)
          (setf as (coerce (realpart (zabs s1r s1i)) 'double-float))
          (setf acs (- (f2cl-lib:flog as) zrr))
          (setf nz (f2cl-lib:int-add nz 1))
          (setf (f2cl-lib:fref yr (i) ((1 n))) zeror)
          (setf (f2cl-lib:fref yi (i) ((1 n))) zeroi)
          (if (< acs (- elim)) (go label10))
          (multiple-value-bind (var-0 var-1 var-2 var-3 var-4)
              (zlog s1r s1i csr csi idum)
            (declare (ignore var-0 var-1))
            (setf csr var-2)
            (setf csi var-3)
            (setf idum var-4))
          (setf csr (- csr zrr))
          (setf csi (- csi zri))
          (setf str (/ (exp csr) tol))
          (setf csr (* str (cos csi)))
          (setf csi (* str (sin csi)))
          (multiple-value-bind (var-0 var-1 var-2 var-3 var-4)
              (zuchk csr csi nw ascle tol)
            (declare (ignore var-0 var-1 var-3 var-4))
            (setf nw var-2))
          (if (/= nw 0) (go label10))
          (setf (f2cl-lib:fref yr (i) ((1 n))) csr)
          (setf (f2cl-lib:fref yi (i) ((1 n))) csi)
          (setf ic i)
          (setf nz (f2cl-lib:int-sub nz 1))
         label10))
      (if (= n 1) (go end_label))
      (if (> ic 1) (go label20))
      (setf (f2cl-lib:fref yr (1) ((1 n))) zeror)
      (setf (f2cl-lib:fref yi (1) ((1 n))) zeroi)
      (setf nz 2)
     label20
      (if (= n 2) (go end_label))
      (if (= nz 0) (go end_label))
      (setf fn (+ fnu 1.0))
      (setf ckr (* fn rzr))
      (setf cki (* fn rzi))
      (setf s1r (f2cl-lib:fref cyr (1) ((1 2))))
      (setf s1i (f2cl-lib:fref cyi (1) ((1 2))))
      (setf s2r (f2cl-lib:fref cyr (2) ((1 2))))
      (setf s2i (f2cl-lib:fref cyi (2) ((1 2))))
      (setf helim (* 0.5 elim))
      (setf elm (exp (- elim)))
      (setf celmr elm)
      (setf zdr zrr)
      (setf zdi zri)
      (f2cl-lib:fdo (i 3 (f2cl-lib:int-add i 1))
                    ((> i n) nil)
        (tagbody
          (setf kk i)
          (setf csr s2r)
          (setf csi s2i)
          (setf s2r (+ (- (* ckr csr) (* cki csi)) s1r))
          (setf s2i (+ (* cki csr) (* ckr csi) s1i))
          (setf s1r csr)
          (setf s1i csi)
          (setf ckr (+ ckr rzr))
          (setf cki (+ cki rzi))
          (setf as (coerce (realpart (zabs s2r s2i)) 'double-float))
          (setf alas (f2cl-lib:flog as))
          (setf acs (- alas zdr))
          (setf nz (f2cl-lib:int-add nz 1))
          (setf (f2cl-lib:fref yr (i) ((1 n))) zeror)
          (setf (f2cl-lib:fref yi (i) ((1 n))) zeroi)
          (if (< acs (- elim)) (go label25))
          (multiple-value-bind (var-0 var-1 var-2 var-3 var-4)
              (zlog s2r s2i csr csi idum)
            (declare (ignore var-0 var-1))
            (setf csr var-2)
            (setf csi var-3)
            (setf idum var-4))
          (setf csr (- csr zdr))
          (setf csi (- csi zdi))
          (setf str (/ (exp csr) tol))
          (setf csr (* str (cos csi)))
          (setf csi (* str (sin csi)))
          (multiple-value-bind (var-0 var-1 var-2 var-3 var-4)
              (zuchk csr csi nw ascle tol)
            (declare (ignore var-0 var-1 var-3 var-4))
            (setf nw var-2))
          (if (/= nw 0) (go label25))
          (setf (f2cl-lib:fref yr (i) ((1 n))) csr)
          (setf (f2cl-lib:fref yi (i) ((1 n))) csi)
          (setf nz (f2cl-lib:int-sub nz 1))
          (if (= ic (f2cl-lib:int-sub kk 1)) (go label40))
          (setf ic kk)
          (go label30)
         label25
          (if (< alas helim) (go label30))
          (setf zdr (- zdr elim))
          (setf s1r (* s1r celmr))
          (setf s1i (* s1i celmr))
          (setf s2r (* s2r celmr))
          (setf s2i (* s2i celmr))
         label30))
      (setf nz n)
      (if (= ic n) (setf nz (f2cl-lib:int-sub n 1)))
      (go label45)
     label40
      (setf nz (f2cl-lib:int-sub kk 2))
     label45
      (f2cl-lib:fdo (i 1 (f2cl-lib:int-add i 1))
                    ((> i nz) nil)
        (tagbody
          (setf (f2cl-lib:fref yr (i) ((1 n))) zeror)
          (setf (f2cl-lib:fref yi (i) ((1 n))) zeroi)
         label50))
      (go end_label)
     end_label
      (return (values nil nil nil nil nil nil nz nil nil nil nil nil)))))

(in-package #-gcl #:cl-user #+gcl "CL-USER")
#+#.(cl:if (cl:find-package '#:f2cl) '(and) '(or))
(eval-when (:load-toplevel :compile-toplevel :execute)
  (setf (gethash 'fortran-to-lisp::zkscl fortran-to-lisp::*f2cl-function-info*)
          (fortran-to-lisp::make-f2cl-finfo
           :arg-types '((double-float) (double-float) (double-float)
                        (fortran-to-lisp::integer4)
                        (simple-array double-float (*))
                        (simple-array double-float (*))
                        (fortran-to-lisp::integer4) (double-float)
                        (double-float) (double-float) (double-float)
                        (double-float))
           :return-values '(nil nil nil nil nil nil fortran-to-lisp::nz nil nil
                            nil nil nil)
           :calls '(fortran-to-lisp::zuchk fortran-to-lisp::zlog
                    fortran-to-lisp::zabs))))

