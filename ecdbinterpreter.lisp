;;;
;;; ECDB: Extended Clause Database System
;;; Tables of RAHD-generated clauses and exporting functions.
;;;
;;; ** The communication language for the ECDB **
;;;
;;;     Type and class definitions.
;;;     Parsing instructions and dispatching commands.
;;;
;;; Written by Florent Kirchner
;;; Postdoctoral Researcher, INRIA Rennes - Bretagne Atlantique, France
;;; Contact: florent.kirchner@lix.polytechnique.fr, www.lix.polytechnique.fr/~fkirchner
;;; 
;;; This file: began on         november-2-2010,
;;;            last updated on  november-3-2010.
;;;

(in-package ecdb)

;;;
;;; MALFORMED-COM: A condition raised when commands are not correctly
;;; initialized. Used in the *-COM class definitions.
;;;
;;; In Lisp, a condition is an object that represents a situation, usually for
;;; signalling purposes. It is analogous to Caml, or Python exceptions.
;;;

(define-condition malformed-com (error) 
  ((com-msg :type string
            :initarg :com-msg
            :reader com-msg)))

;;;
;;; Three kinds of commands can be received from outside tools:
;;;     FOREIGN-RAHD-COM, to issue RAHD commands;
;;;     FOREIGN-ECDB-COM, to issue ECDB commands;
;;;     FOREIGN-SEXP, to issue general Lisp commands. TODO: Only allow in DEBUG mode.
;;;
 
;;; We start with the abstract superclass.
(defclass foreign-com () 
  ((com-body :type list
             :initarg :body
             :accessor body))) ; Later: check that the slot is bound with SLOT_BOUNDP

;;; RAHD-COM-KIND: A RAHD command kind. It can be either 
;;;     - an instruction for setting the goal-set (RAHD-GS),
;;;     - or an instruction to launch the waterfall (RAHD-GO)
(deftype rahd-com-kind ()
  '(member rahd-gs rahd-go))

;;; A RAHD command pairs a kind with a command body (an s-expression).
(defclass foreign-rahd-com (foreign-com)
  ((com-kind :type rahd-com-kind
             :initarg :kind
             :initform (error 'malformed-com :com-msg "Must supply a RAHD command kind: RAHD-GS, or RAHD-GO.")
             :accessor kind)))

;;; ECDB-COM-KIND: An ECDB command kind, which can be either 
;;;     - an instruction for querying the db (ECDB-QUERY)
;;;     - or an instruction to provide a case cerificate (ECDB-CERTIFICATE)
(deftype ecdb-com-kind ()
  '(member ecdb-query ecdb-certificate))

;;; An ECDB command pairs a kind with a command body (an s-expression).
(defclass foreign-ecdb-com (foreign-com)
  ((com-kind :type ecdb-com-kind
             :initarg :kind
             :initform (error 'malformed-com :com-msg "Must supply an ECDB command kind: ECDB-QUERY, or ECDB-CERTIFICATE.")
             :accessor kind)))

;;; An SEXP commandonly has a body.
(defclass foreign-sexp-com (foreign-com)
  ((com-body :type list
             :initarg :command
             :initform (error 'malformed-com :com-msg "Must supply an s-expression.")
             :accessor body)))

;;; 
;;; SEXP-NODEBUG and UNKNOWN-COM: Signals thrown in the input sanitizing phase.
;;;

(define-condition sexp-nodebug (error) ())

(define-condition unknown-com (error) ())

;;;
;;; IMPORT-FOREIGN: Takes an external command, and evaluates it into a
;;; *-foreign-com object. 
;;; com is a string argument of the form:
;;;     rahd-com :kind 'rahd-gs :body '((= x 1) (> x 1) (< x 1))
;;; TODO: write a proper parser.
;;;

(defun import-foreign (com)
  (handler-case 
   (progn 
    (if (< (length com) 9)
        (error 'unknown-com))
    (if (and (string-equal com "sexp-com " :end1 9)
             (not +ecdb-debug+))
        (error 'sexp-nodebug))
    (if (and (string-not-equal com "rahd-com " :end1 9)
             (string-not-equal com "ecdb-com " :end1 9)
             (string-not-equal com "sexp-com " :end1 9))
        (error 'unknown-com))
    (let ((complete-com (format nil "(make-instance \'foreign-~a)" com)))
         (eval (read-from-string complete-com))))
    (malformed-com (mc)
                   (format t "[ECDB]: Malformed command.~%")
                   (format t "       ~a" (com-msg mc))
                   nil)
    (sexp-nodebug ()
                  (format t "[ECDB]: Unauthorized use of sexp command (set debug mode to enable).~%")
                  nil)
    (unknown-com ()
                 (format t "[ECDB]: Malformed command.~%")
                 (format t "       ~a" com)
                 ())))

; [HS] CLASS-OF: Returns the class of which the object is a direct instance. 
; [HS]          Check object class membership with TYPE-OF.

