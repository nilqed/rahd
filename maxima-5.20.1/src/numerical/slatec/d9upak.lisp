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


(defun d9upak (x y n)
  (declare (type (integer) n) (type (double-float) y x))
  (prog ((absx 0.0))
    (declare (type (double-float) absx))
    (setf absx (f2cl-lib:dabs x))
    (setf n 0)
    (setf y 0.0)
    (if (= x 0.0) (go end_label))
   label10
    (if (>= absx 0.5) (go label20))
    (setf n (f2cl-lib:int-sub n 1))
    (setf absx (* absx 2.0))
    (go label10)
   label20
    (if (< absx 1.0) (go label30))
    (setf n (f2cl-lib:int-add n 1))
    (setf absx (* absx 0.5))
    (go label20)
   label30
    (setf y (coerce (f2cl-lib:dsign absx x) 'double-float))
    (go end_label)
   end_label
    (return (values nil y n))))

(in-package #-gcl #:cl-user #+gcl "CL-USER")
#+#.(cl:if (cl:find-package '#:f2cl) '(and) '(or))
(eval-when (:load-toplevel :compile-toplevel :execute)
  (setf (gethash 'fortran-to-lisp::d9upak
                 fortran-to-lisp::*f2cl-function-info*)
          (fortran-to-lisp::make-f2cl-finfo
           :arg-types '((double-float) (double-float) (integer))
           :return-values '(nil fortran-to-lisp::y fortran-to-lisp::n)
           :calls 'nil)))
