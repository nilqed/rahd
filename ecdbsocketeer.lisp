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
;;;     *ECDB-DIALECT* lanaguage of the output buffer.
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

(defun init-and-wait (&key (host *default-host*) (port *default-port*))
  (let ((master-socket
          (socket-listen host port
                         :reuse-address t ; ATM, this is buggy and won't work as documented
                         :element-type 'character
                         )))
    (wait-for-input master-socket)
    (setq *ecdb-socket* (socket-accept master-socket))))

;;;
;;; COLLECT-INPUT: Read a stream from a socket, and put it in a buffer.
;;;
;;; The :with keyword initializes varaibles that are local to the loop, :while
;;; provides a termination check, and :doing is used to provide an implicit
;;; progn.
;;;

(defun collect-input (socket buffer)
  (loop
    :with stream = (socket-stream socket)
    :with char
    :while (listen stream)
    :doing
    (setq char (read-char stream))
    (vector-push-extend char buffer)))

;;;
;;; SEND-OUTPUT: Given a socket and a buffer, send the contents of the second
;;; to the first.
;;;

(defun send-output (socket buffer)
  (format (socket-stream socket) "~a~%" buffer)
  (force-output (socket-stream socket)))

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
    (cond ((eq *ecdb-dialect* 'coq)
           (setq res (make-coq-clause res)))
          (t t))
    (append-string-to-buffer (format nil "~a" res) outb)))

;;;
;;; PROCESS-SINGLE-INPUT: Collect input from socket, process it, and clear the
;;; buffer.
;;;

(defun process-single-input (&optional (socket *ecdb-socket*) 
                                       (inb *in-buffer*) (outb *out-buffer*))
  (collect-input socket inb)
  (format t "[ECDB] Incoming message: \"~a\".~%" inb)
  (compute-query inb outb)
  (send-output socket (format nil "~a~%" outb))
  (reset-buffer inb)
  (reset-buffer outb))

;;;
;;; RUN! is the main function of the ECDB implementation. It polls the socket
;;; stream until it returns :eof, in which case it will exit cleanly.
;;;

(defun run! ()
    (init-and-wait)
    (loop
      :with stream = (socket-stream *ecdb-socket*)
      :while (not (eq (peek-char t stream nil :eof) :eof))
      :doing (process-single-input))
    (socket-close *ecdb-socket*))

;;;
;;; Examples
;;;

;;; To run this and other code snippets, remove the #() line in front

;#+ ()


