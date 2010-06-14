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
;;;           (:coerce-assigns :as-needed) (:array-type ':array)
;;;           (:array-slicing t) (:declare-common nil)
;;;           (:float-format double-float))

(in-package :slatec)


(defun dqwgts (x a b alfa beta integr)
  (declare (type (f2cl-lib:integer4) integr)
           (type (double-float) beta alfa b a x))
  (prog ((bmx 0.0) (xma 0.0) (dqwgts 0.0))
    (declare (type (double-float) dqwgts xma bmx))
    (setf xma (- x a))
    (setf bmx (- b x))
    (setf dqwgts (* (expt xma alfa) (expt bmx beta)))
    (f2cl-lib:computed-goto (label40 label10 label20 label30) integr)
   label10
    (setf dqwgts (* dqwgts (f2cl-lib:flog xma)))
    (go label40)
   label20
    (setf dqwgts (* dqwgts (f2cl-lib:flog bmx)))
    (go label40)
   label30
    (setf dqwgts (* dqwgts (f2cl-lib:flog xma) (f2cl-lib:flog bmx)))
   label40
    (go end_label)
   end_label
    (return (values dqwgts nil nil nil nil nil nil))))

(in-package #-gcl #:cl-user #+gcl "CL-USER")
#+#.(cl:if (cl:find-package '#:f2cl) '(and) '(or))
(eval-when (:load-toplevel :compile-toplevel :execute)
  (setf (gethash 'fortran-to-lisp::dqwgts
                 fortran-to-lisp::*f2cl-function-info*)
          (fortran-to-lisp::make-f2cl-finfo
           :arg-types '((double-float) (double-float) (double-float)
                        (double-float) (double-float)
                        (fortran-to-lisp::integer4))
           :return-values '(nil nil nil nil nil nil)
           :calls 'nil)))

