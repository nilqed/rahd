;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; Front end interface routines for communicating problems to RAHD in a
;;;  nice computer-algebra-like format and interacting with the prover
;;;  via a safe (not raw Lisp!) REPL.
;;;
;;; Written by Grant Olney Passmore
;;; Postdoc, Cambridge-Edinburgh EPSRC grant
;;;   ``Automatic Proof Procedures for Polynomials and Special Functions.''
;;;
;;; The following institutions have provided support for RAHD development
;;;  through funding the following positions for me (Passmore):
;;;    - Ph.D. Student, University of Edinburgh,
;;;    - Visiting Fellow, SRI International,
;;;    - Research Intern, Microsoft Research,
;;;    - Visiting Researcher, INRIA/IRISA.
;;;
;;; These positions have been crucial to RAHD progress and we thank the host 
;;;  institutions and groups very much for their support and encouragement.
;;;
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/.
;;; 
;;; This file: began on         1-November-2010,
;;;            last updated on  5-November-2010.
;;;

;;;
;;; The final parsing routines below are based on Juliusz Chroboczek's
;;;  Common Lisp YACC library (c) Juliusz Chroboczek, 2009.  
;;; Thank you, Juliusz for this excellent tool!
;;;

(load "lib/cl-yacc-0.3/yacc")

;;;
;;; Error condition for lexing.
;;;

(define-condition lex-error (error)
  ((message
    :initarg :message
    :accessor lex-error-message
    :initform nil
    :documentation "Text message indicating what went wrong with the lexing.")
   (value
    :initarg :value
    :accessor lex-error-value
    :initform nil
    :documentation "The value of the character for which the error is signalled.")
   (position
    :initarg :position
    :accessor lex-error-position
    :initform nil
    :documentation "The position of the character for which the error was
  signalled."))
  (:report 
   (lambda (w stream)
     (format stream
             "~A ~A" (lex-error-message w) (lex-error-value w)))))

(defun lex-error (message &key value position)
  (error 'lex-error
         :message message
         :value value
         :position position))

;;;
;;; Display a prompt and read its input (ended with a newline),
;;;  returning it as a string.
;;;

(defun prompt-and-read (p)
  (finish-output)
  (format *standard-output* p)
  (finish-output)
  ;(clear-input)
  (read-line *standard-input* nil 'EOF))

;;;
;;; A simple command string parser for RAHD interaction.
;;; This uses the first space in the string to separate
;;; function name from argument.  We are only monadic now :-).
;;;

(defun cmd-pair (s)
  (if (equal s 'EOF) '(EOF nil)
    (let ((space-pos (position '#\Space s)))
      (if space-pos
          (cons (subseq s 0 space-pos)
                (subseq s (1+ space-pos) (length s)))
        (cons s "")))))

;;;
;;; Print a RAHD list of conjunctions in order, giving numbers
;;;  to each conjunct.
;;;

(defun show-f-infix (f)
  (cond ((null f) (fmt 0 "No formula asserted.~%~%"))
        (t (fmt 0 "Current formula:~%~%")
           (let ((count 0))
             (dolist (i f)
               (fmt 0 " H~A. ~A.~%"
                    count
                    (f-infix-str i))
               (setq count (1+ count))))
           (fmt 0 "~%"))))

;;;
;;; Simple read-eval-print loop for RAHD interaction.
;;;

(defun r-repl ()
  (handler-bind 
   ((yacc:yacc-parse-error 
     #'(lambda (c)
         (let ((restart (find-restart 'continue-with-new-cmd)))
           (when restart
             (fmt 0 "Parser error: ~A.~%~%" c)
             (invoke-restart restart)))))
    (lex-error 
     #'(lambda (c)
         (let ((restart (find-restart 'continue-with-new-cmd)))
           (when restart
             (fmt 0 "Lexer error: ~A.~%Have you declared all variables?
  (Try 'help vars')~%~%" c)
             (invoke-restart restart))))))
   (let ((exit?) (vars-lst) (asserted-atoms-lst) 
         (prover-opts '("print-infix")) (verbosity 0))
     (while (not exit?)
       (let ((s (cmd-pair (prompt-and-read "RAHD!> "))))
         (let ((cmd (car s)) (arg (cdr s)))
           (cond
            ((or (equal cmd "quit")
                 (equal cmd 'EOF))
             (setq exit? t))
            ((equal cmd "vars")
             (cond ((equal arg "")
                    (fmt 0 "Current vars: ~A.~%~%" vars-lst))
                   (t (setq vars-lst (p-vars-lst arg))
                      (fmt 0 "Current vars: ~A.~%~%" vars-lst))))
            ((equal cmd "assert")
             (with-simple-restart (continue-with-new-cmd
                                   "Continue and enter a new RAHD command.")
                                  (let ((prover-formula
                                         (atom-lst (p-formula-str arg :vars-lst vars-lst))))
                                    (setq asserted-atoms-lst
                                          (append prover-formula asserted-atoms-lst))
                                    (fmt 0 "Formula asserted: ~A.~%~%"
                                         prover-formula))))
            ((equal cmd "options")
             (fmt 0 "Prover options: ~A.~%~%" prover-opts))
            ((equal cmd "set?")
             (fmt 0 "Prover option ~A is ~A.~%~%"
                  arg (if (member arg prover-opts :test 'equal)
                          "set" "unset")))
            ((equal cmd "set")
             (push arg prover-opts)
             (fmt 0 "Prover option ~A set.~%~%" arg))
            ((equal cmd "unset")
             (setq prover-opts
                   (remove-if #'(lambda (x) (equal x arg))
                              prover-opts))
             (fmt 0 "Prover option ~A unset.~%~%" arg))
            ((equal cmd "verbosity")
             (if (equal arg "")
                 (fmt 0 "Verbosity level is ~A.~%~%" verbosity)
               (let ((v-c (car (p-rational arg))))
                 (cond (v-c (setq verbosity v-c)
                            (fmt 0 "Verbosity level is now ~A.~%~%" arg))
                       (t (fmt 0 "Input error: Verbosity level must be a rational number.~%~%"))))))
            ((equal cmd "check")
             (if (not asserted-atoms-lst)
                 (fmt 0 "Prover error: No atoms asserted.~%~%")
               (let ((result (check (mapcar #'list (reverse asserted-atoms-lst))
                                    :from-repl t
                                    :print-model 
                                    (member "print-model" prover-opts :test 'equal)
                                    :search-model
                                    (member "search-model" prover-opts :test 'equal)
                                    :search-model*
                                    (member "search-model*" prover-opts :test 'equal)
                                    :verbosity verbosity)
                                    ))
                 (fmt 0 " ~A~%~%" result))))
            ((equal cmd "show")
             (if (member "print-infix" prover-opts :test 'equal)
                 (show-f-infix (reverse asserted-atoms-lst))
               (fmt 0 "Current formula: ~A.~%~%" 
                    asserted-atoms-lst)))
            ((equal cmd "reset")
             (setq asserted-atoms-lst nil)
             (fmt 0 "Current formula reset.~%~%"))
            ((equal cmd "lisp")
             (fmt 0 "Value: ~A.~%~%" (eval (read-from-string arg))))
            ((equal cmd "help")
             (cond ((equal arg "")
                    (fmt 0 "Help with RAHD shell.  Try 'help <keyword>' ~
  where keywords are:~%
   assert check help lisp options quit reset set show
   unset vars verbosity. ~%~%"))
                   ((equal arg "assert")
                    (fmt 0 "Usage: assert <formula>~%
 Asserts a formula as an assumption in the current context.~%
 Note that an asserted formula must be either a single literal 
  or a conjunction of literals.
 Also, all variables in the formula must be declared.

 Example:
  assert x^2 + (x - z)^2 > 0 /\\ z >= 5

 * See vars for more on variable declaration.
 * See check for checking the satisfiability of a context.
 * See show for viewing the current context.
 * See reset for clearing the current context.~%~%"))
                   ((equal arg "help")
                    (fmt 0 "Usage: help <keyword>~%
 Invoke 'help' with no arguments for possible keywords.~%~%"))))
            ((equal cmd ""))
            (t (fmt 0 "Input error: Command '~A' not understood.~%~%" cmd)
               ))))))
   (fmt 0 "Goodbye.~%")))

;;;
;;; A simple monolithic problem-oriented interface for MetiTarski and
;;;  other automated tools.
;;;

(defun p-repl ()
  (handler-bind 
   ((yacc:yacc-parse-error 
     #'(lambda (c)
         (let ((restart (find-restart 'continue-with-new-cmd)))
           (when restart
             (fmt 0 "Parser error: ~A.~%~%" c)
             (invoke-restart restart)))))
    (lex-error 
     #'(lambda (c)
         (let ((restart (find-restart 'continue-with-new-cmd)))
           (when restart
             (fmt 0 "Lexer error: ~A.~%Have you declared all~
  variables?~%~%" c)
             (invoke-restart restart))))))
   (let ((exit?))
     (while (not exit?)
       (let ((vars-lst
              (let ((vl-attempt (prompt-and-read "~%v>~%")))
                (if (or (equal vl-attempt "quit")
                        (equal vl-attempt 'EOF))
                    (setq exit? t)
                  (p-vars-lst vl-attempt)))))
         (when (not exit?)
           (let ((f-attempt (prompt-and-read "~%f>~%")))
             (with-simple-restart 
              (continue-with-new-cmd
               "Continue and enter a new RAHD formula.")
              (let ((prover-formula 
                     (reverse (let ((raw-f 
                                     (p-formula-str f-attempt 
                                                    :vars-lst
                                                    vars-lst)))
                                (mapcar #'list (elim-ands raw-f))))))
                (fmt 2 "Formula: ~A.~%~%" prover-formula)
                (format *standard-output* 
                        "~A~%" (check prover-formula 
                                      :from-repl t
                                      :verbosity 0
                                      :skip-cad t
                                      :skip-factor-sign t)))))))))))

;;;
;;; F-INFIX-STR: Given a RAHD formula in prover notation, build
;;;  an infix string of it which can be read back by our parser.
;;;

(defun f-infix-str (p)
  (cond ((null p) "")
        ((not (consp p)) (format nil "~A" p))
        (t (let ((op (car p))
                 (x (cadr p))
                 (y (caddr p)))
             (format nil "~A ~A ~A"
                     (f-infix-str x)
                     (f-infix-str op)
                     (f-infix-str y))))))

;;;
;;; ELIM-ANDS: Eliminate explicit ANDs from a purely conjunctive 
;;;  input formula consisting of conjoined atoms and negated atoms.
;;;

(defun elim-ands (f)
  (cond ((not (consp f)) f)
        ((= (length f) 3)
         (let ((op (car f))
               (x (cadr f))
               (y (caddr f)))
           (case op
             (AND (union (elim-ands x)
                         (elim-ands y)))
             ((>= > = < <=)
              (list f)))))
        (t (list f))))

;;;
;;; ATOM-LST: Given an S-expression formula which is either a single
;;;  literal or a conjunction of literals, separate it out into a
;;;  list of literals.
;;;

(defun atom-lst (f)
  (if (eq (car f) 'AND)
      (elim-ands f)
    (list f)))

;;;
;;; Simple QEPCAD-B-like interface to RAHD.
;;; *Incomplete.
;;;

(defun q-repl ()
  (let ((exit?) (i 0) (f) (finished?))
    (while (not exit?)
      (setq exit? t)
      (fmt 0 "~% ------------------------------------------------~%")
      (fmt 0 "    RAHD QEPCAD-B front-end emulation: Round ~A" i)
      (fmt 0 "~% ------------------------------------------------~%")
      (prompt-and-read "Enter an informal description  between '[' and ']':~%")
      (prompt-and-read "Enter a variable list:~%")
      (prompt-and-read "Enter the number of free variables:~%")
      (setq f (prompt-and-read "Enter a prenex formula:~%"))
      (q-opt "Before Normalization >~%")
      (q-opt "At the end of projection phase >~%")
      (q-opt "Before Choice >~%")
      (q-opt "Before Solution >~%")
      (fmt 0 "~% Formula to send RAHD: ~A.~%~%" f)
      )))

;;;
;;; Q-OPT-PAR: QEPCAD-B style option prompt.
;;;  This involves repeating the same question until
;;;   either `go',`finish', or `continue' is input.
;;;  We accept an option `finished' which turns this
;;;   function into a no-op.
;;;

(defun q-opt-par (p &key finished?)
  (let ((exit? finished?) (out))
    (while (not exit?)
      (let ((s (prompt-and-read p)))
        (fmt 0 "~%")
        (when (or (equal s "go")
                  (equal s "finish")
                  (equal s "continue"))
          (setq exit? t)
          (setq out s))))
    out))

(defmacro q-opt (p)
  `(let ((s (q-opt-par ,p)))
     (cond ((equal s "finish")
            (setq finished? t))
           ((equal s "continue")
            (setq exit? nil)))))

;;;
;;; Parse an infix RAHD input formula string into an S-expression.
;;;
;;; Note that variables are case-insensitive.
;;;

;;;
;;; Parse a list of variables separated by spaces.
;;;

(defun p-vars-lst (s)
  (remove-if #'(lambda (x)
                 (or (equal x " ") (equal x "")))
             (make-word-lst (string-upcase s))))

;;;
;;; Given a list of var-strs and a string S, return a pair
;;;  (var-str . rst-s) if S begins with var-str.
;;;

(defun p-var (s vars-lst)
  (if (equal s "") '(nil . "")
    (let ((var-found? nil) (v-str) (s-rst))
      (loop for c in vars-lst until var-found? do
        (let ((v-match? (p-match-prefix c s)))
          (when v-match?
            (setq var-found? t)
            (setq v-str c)
            (setq s-rst v-match?))))
      (if var-found?
          (cons (string-upcase v-str) s-rst)
        (cons nil s)))))

;;;
;;; Given two strings S and PREFIX, check to see if PREFIX is indeed a prefix
;;; of S, ignoring case distinctions.  If it is, then return the remainder of 
;;; S once PREFIX has been removed.  Otherwise, return nil.
;;;

(defun p-match-prefix (prefix s)
  (let ((lp (length prefix))
        (ls (length s)))
    (when (>= ls lp)
      (let ((c (subseq s 0 lp)))
        (when (equal (string-upcase c) 
                     (string-upcase prefix))
          (subseq s lp ls))))))

;;;
;;; P-RATIONAL (s): Given a string beginning with a rational number, "rS," where
;;; S begins with some non-numeric character, return (r . S), where r is a Lisp rational.
;;;

(defun p-rational (s)
  (let* ((parse-num-0 (p-int s))
	 (numerator (car parse-num-0))
	 (num-0-rst (cdr parse-num-0)))
    (if (and (> (length num-0-rst) 1) 
	     (string-equal (subseq num-0-rst 0 1) "/"))
	(let* ((parse-num-1 (p-int (subseq num-0-rst 1)))
	       (denominator (car parse-num-1))
	       (num-1-rst (cdr parse-num-1)))
	  (cons (/ numerator denominator) num-1-rst))
      (cons numerator num-0-rst))))
			
;;;
;;; P-INT (s): Given a string beginning with a numeral, "nnn...nS" where S begins
;;; with some non-numeric character, return a list: (nnn...n . S) where nnn...n is "nnn...n" 
;;; converted to a Lisp integer.
;;;

(defun p-int (s)
  (let ((neg? nil))
    (when (equal (char s 0) #\-)
      (setq neg? t)
      (setq s (subseq s 1 (length s))))
  (let ((num "") (c 0))
    (loop for char across s
	  do (if (not (member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))) (return t)
	       (progn (setq num (concatenate 'string num (string char)))
		      (setq c (1+ c)))))
    (if (> c 0) (cons (* (if neg? -1 1) (parse-integer num)) (subseq s c)) `(nil . ,s)))))

;;;
;;; Lexical analysis:
;;;

(use-package '#:yacc)

(defmacro chunk-char (c)
  `(progn
     (fmt 11 "~% Chunking char: ~A." ,c)
     (setq out (cons ,c out))
     (setq s (subseq s 1 l-s))))

(defmacro chunk-prefix (p)
  `(progn
     (fmt 11 "~% Chunking prefix: ~A." ,p)
     (setq out (cons ,p out))
     (setq s (subseq s ,(length p) l-s))))

;;;
;;; Convert a RAHD formula string into a list of symbols.  These
;;;  will then be used to generate the lexer thunk.
;;;
;;; We return a list '(err? . result) where err? is t iff
;;;  there was an unexpected symbol.
;;;

(defun str-to-lex-syms (s vars-lst) ; vars-lst is list of strings
  (let ((out) (lex-err))
    (while (and (not (equal s "")) (not lex-err))
      (let ((c (char s 0)) (l-s (length s)))
        (let ((peek-1-c (if (> l-s 1) (char s 1)))
              (peek-2-c (if (> l-s 2) (char s 2))))
          (cond ((and (equal l-s 1) 
                      (member c '(#\+ #\- #\* #\( #\) #\[ #\] #\= #\> #\< #\^ #\~)))
                 (chunk-char c))
                ((member c '(#\+ #\* #\( #\) #\[ #\] #\^ #\~))
                 (chunk-char c))
                ((and (equal c #\-) 
                      (not (member peek-1-c 
                                   '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))))
                     (chunk-char c))
                ((or (equal c '#\Space) (equal c '#\Newline))
                 (setq s (subseq s 1 l-s)))
                ((equal c #\=)
                 (cond ((and (equal peek-1-c '#\=)
                             (equal peek-2-c '#\>))
                        (chunk-prefix "==>"))
                       (t (chunk-char c))))
                ((equal c '#\>)
                 (cond ((equal peek-1-c '#\=)
                        (chunk-prefix ">="))
                       (t (chunk-char c))))
                ((equal c '#\<)
                 (cond ((equal peek-1-c '#\=)
                        (chunk-prefix "<="))
                       (t (chunk-char c))))
                ((equal c '#\!)
                 (cond ((equal peek-1-c '#\=)
                        (chunk-prefix "!="))
                       (t (chunk-char c))))
                ((equal c '#\/)
                 (cond ((equal peek-1-c '#\=)
                        (chunk-prefix "/="))
                       ((equal peek-1-c '#\\)
                        (chunk-prefix "/\\"))
                       (t (chunk-char c))))
                ((equal c '#\\)
                 (cond ((equal peek-1-c '#\/)
                        (chunk-prefix "\\/"))
                       (t (chunk-char c))))
                (t (let ((rat? (p-rational s)))
                     (if (car rat?)
                         (progn 
                           (setq out (cons (car rat?) out))
                           (setq s (cdr rat?)))
                       (let ((var? (p-var s vars-lst)))
                         (if (car var?)
                             (progn
                               (setq out (cons (car var?) out))
                               (setq s (cdr var?)))
                           (lex-error "Unexpected symbol" 
                                      :value c))))))
                ))
               ))
      (mapcar #'(lambda (x)
                  (cond ((symbolp x) x)
                        ((characterp x)
                         (intern (string x)))
                        ((rationalp x)
                         x)
                        ((string x)
                         (intern x))))
              (reverse out))))
                       
(defun lst-lexer (list)
  #'(lambda ()
      (let ((value (pop list)))
        (if (null value)
            (values nil nil)
          (let ((terminal
                 (cond ((member 
                         value 
                         '(+ - * / |(| |)| = > >= <= < ==> |/\\| |\\/| |~| |[|
                             |]| ^ /= !=)) value)
                       ((integerp value) 'int)
                       ((rationalp value) 'rational)
                       ((symbolp value) 'var)
                       (t (lex-error "[Lex-1] Unexpected symbol" 
                                     :value value)))))
            (values terminal value))))))

;;;
;;; The parser for infix RAHD formula strings.
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)

  (defun i2p (a b c)
    "Infix to prefix for /\\, \\/, ==>, ... ."
    (list 
     (case b
       (/\\ 'and)
       (\\/ 'or)
       (==> 'implies)
       (^ 'expt)
       (otherwise b))
          a c))

  (defun i2p-neq (a b c)
    `(not (= ,a ,c)))

  (defun i2p-expt (a b c)
    (declare (ignore b))
    (poly-expand-expts 
     (list 'EXPT a c)))

  (defun k-2-3 (a b c)
    "Second out of three"
    (declare (ignore a c))
    b)
  
  (defun neg (a b)
    (case a
      (- (list '- 0 b))
      (~ (list 'not b)))))

(yacc:define-parser qf-parser
  (:start-symbol qf-formula)
  (:terminals 
   (rational int var + - * = ==> |/\\| |\\/| |~| 
             |(| |)| > >= = /= != <= < / ^ |[| |]|))
  (:precedence 
   ((:left ~) (:left |/\\|) (:left |\\/|) (:left ^) 
    (:left = /= > >= < <=)
    (:left * /) (:left + -) (:left ==>)))

  (qf-formula
   atom
   (~ qf-formula #'neg)
   (qf-formula ==> qf-formula #'i2p)
   (qf-formula |/\\| qf-formula #'i2p)
   (qf-formula |\\/| qf-formula #'i2p)
   (|[| qf-formula |]| #'k-2-3)
   (|(| qf-formula |)| #'k-2-3))

  (atom
   (poly = poly #'i2p)
   (poly /= poly #'i2p-neq)
   (poly != poly #'i2p-neq)
   (poly > poly #'i2p)
   (poly >= poly #'i2p)
   (poly < poly #'i2p)
   (poly <= poly #'i2p))

  (poly
   var                                  ; implicit action #'identity
   int
   rational
   (poly + poly #'i2p)
   (poly - poly #'i2p)
   (poly * poly #'i2p)
   (poly ^ int #'i2p-expt)
   (|(| poly |)| #'k-2-3))
)

;;;
;;; Parser only for conjunctive formulae.
;;;


(yacc:define-parser qf-conj-parser
  (:start-symbol qf-formula)
  (:terminals 
   (rational int var + - * = ==> |/\\| |\\/| |~| 
             |(| |)| > >= = /= != <= < / ^ |[| |]|))
  (:precedence 
   ((:left ~) (:left |/\\|) (:left |\\/|) (:left ^) 
    (:left = /= > >= < <=)
    (:left * /) (:left + -) (:left ==>)))

  (qf-formula
   atom
   (~ atom #'neg)
   (qf-formula |/\\| qf-formula #'i2p)
   (|[| qf-formula |]| #'k-2-3)
   (|(| qf-formula |)| #'k-2-3))

  (atom
   (poly = poly #'i2p)
   (poly /= poly #'i2p-neq)
   (poly != poly #'i2p-neq)
   (poly > poly #'i2p)
   (poly >= poly #'i2p)
   (poly < poly #'i2p)
   (poly <= poly #'i2p))

  (poly
   var                                  ; implicit action #'identity
   int
   rational
   (poly + poly #'i2p)
   (poly - poly #'i2p)
   (poly * poly #'i2p)
   (poly ^ int #'i2p-expt)
   (|(| poly |)| #'k-2-3))
)


;;;
;;; P-FORMULA-STR: Given a RAHD formula string, parse it into
;;;  an S-expression!
;;;

(defun p-formula-str (s &key vars-str vars-lst)
  (let ((live-vars-lst
         (cond (vars-str (p-vars-lst vars-str))
               (vars-lst vars-lst))))
    (let ((stls (str-to-lex-syms s live-vars-lst)))
      (yacc:parse-with-lexer (lst-lexer stls) 
                             qf-conj-parser))))


;;;
;;; Conjunctive string + vars-str to RAHD CNF.
;;;

(defun p-conj-f (f vs)
  (mapcar #'list
          (elim-ands (p-formula-str f :vars-str vs))))