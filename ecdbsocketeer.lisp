;;;
;;; ECDB: Extended Clause Database System
;;; Tables of RAHD-generated clauses and exporting functions.
;;;
;;; ** The socket mechanism for the database **
;;;
;;;     Initializing and waiting for incoming connections.
;;;     Collecting and processing input.
;;;     Sending output.
;;;     The RUN! function that ties everything together.
;;;
;;; Written by Florent Kirchner
;;; Postdoctoral Researcher, INRIA Rennes - Bretagne Atlantique, France
;;; Contact: florent.kirchner@lix.polytechnique.fr, www.lix.polytechnique.fr/~fkirchner
;;; 
;;; This file: began on         march-29-2010,
;;;            last updated on  april-6-2010.
;;;

(in-package ECDB)

;;;
;;; ECDB serves queries locally. Random port. This could be modularized using
;;; compile-time options.
;;;

(defparameter *default-host* "localhost")
(defparameter *default-port* 7203)

;;;
;;; Global variables: 
;;;     *ECDB-SOCKET* socket, 
;;;     *IN-BUFFER* input buffer,
;;;     *OUT-BUFFER* output buffer,
;;;     *ECDB-DIALECT* language of the output buffer.
;;;

(defparameter *ecdb-socket* nil)

(defparameter *in-buffer* 
  (make-array 5 :element-type 'character :adjustable t :fill-pointer 0))

(defparameter *out-buffer* 
  (make-array 5 :element-type 'character :adjustable t :fill-pointer 0))

(defparameter *ecdb-dialect* 'rahd)

;;;
;;; APPEND-STRING-TO-BUFFER
;;;

(defun append-string-to-buffer (str buffer)
  (map 'nil #'(lambda (c) (vector-push-extend c buffer)) str))

;;;
;;; INIT-AND-WAIT: Socket startup and standby function. Affects *ECDB-SOCKET*
;;; to deal with incoming connections.
;;;

(defun init-and-wait (host port)
  (let ((master-socket
         (usocket:socket-listen host port
                                :reuse-address t
                                :element-type 'character
                                )))
       (usocket:wait-for-input master-socket 
                               :ready-only t)
       (setq *ecdb-socket* (usocket:socket-accept master-socket))))

;;;
;;; COLLECT-INPUT: Read a set of characters from a stream, and push it in a
;;; buffer.
;;;
;;; The :with keyword initializes variables that are local to the loop, :while
;;; provides a termination check, and :doing is used to provide an implicit
;;; progn.
;;;

(defun collect-input (cstream buffer)
  (loop
   :with char
   :while (listen cstream)
   :doing
   (setq char (read-char cstream))
   (vector-push-extend char buffer)))

;;;
;;; SEND-OUTPUT: Given a socket and a buffer, send the contents of the second
;;; to the first.
;;;

(defun send-output (cstream buffer)
  (format cstream "~a~%" buffer)
  (finish-output cstream))

;;;
;;; RESET-BUFFER: fast way to forget about the content of a buffer.
;;;

(defun reset-buffer (buffer)
  (setf (fill-pointer buffer) 0))

;;;
;;; COMPUTE-QUERY: evaluate the s-expression that is in buffer inb, and write
;;; the result in outb.
;;;

(defun compute-query (inb outb)
  (let ((res (eval (read-from-string (format nil "~a" inb)))))
;    (cond ((eq *ecdb-dialect* 'coq)
;           (setq res (make-coq-clause res)))
;          (t t))
    (append-string-to-buffer (format nil "~a" res) outb)))

;;;
;;; PROCESS-SINGLE-INPUT: Collect input from a character stream, process it,
;;; send answer back in a socket, and clear the buffer.
;;;

(defun process-single-input (cstream #|sock|# &optional (inb *in-buffer*) (outb *out-buffer*))
  (collect-input cstream inb)
  (format t "[ECDB] Processing incoming message: \"~a\"...~%" inb)
  (compute-query inb outb)
  (format t "[ECDB] Sending result: \"~a\".~%" outb)
  (send-output cstream outb)
  (reset-buffer inb)
  (reset-buffer outb))

;;;
;;; SERVE is the main function of the ECDB implementation. It polls the socket
;;; stream until it returns :eof, in which case it will exit cleanly.
;;;

(defun serve (&optional (host *default-host*) (port *default-port*))
  (handler-case 
   (progn
    ; set the main passive socket
    (setq *ecdb-socket* (usocket:socket-listen host port 
                                               :reuse-address t
                                               :element-type 'character))
    (usocket:wait-for-input *ecdb-socket* :ready-only t)
    ; once input has been detected, create an active (live) socket
    ; here is where we'll loop if we need multiple threads
    (let* ((sock      (usocket:socket-accept *ecdb-socket*))
           (cstream   (usocket:socket-stream sock)))
          (unwind-protect 
           (loop
            :while (peek-char t cstream nil nil) ;peek-char returns nil upon encountering :eof
            :doing (process-single-input cstream))
           ; cleanup before you go
           (progn (close cstream)
                  (usocket:socket-close sock)
                  (usocket:socket-close *ecdb-socket*)))))
   ;catch exceptions
   (address-in-use-error ()
                         (format t "[ECDB] The address ~a:~a is busy." host port)
                         nil)))

;;;
;;; Examples
;;;

;;; To run this and other code snippets, remove the #() line in front

;#+ ()



