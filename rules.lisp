;;;
;;; RAHD: Real Algebra in High Dimensions v0.6
;;; A proof procedure for the existential theory of real closed fields.
;;;
;;; RAHD ruleset (lemma library) machinery.
;;;
;;; Written by Grant Olney Passmore
;;; Ph.D. Student, University of Edinburgh
;;; Visiting Fellow, SRI International
;;; Contact: g.passmore@ed.ac.uk, http://homepages.inf.ed.ac.uk/s0793114/
;;; 
;;; This file: began on         30-June-2010,
;;;            last updated on  03-July-2010.
;;;

;;;
;;; APPLY-RULESET-TO-CASE: Given a ruleset name and a case, saturate 
;;;  the case with the results of applying the ruleset to the case via 
;;;  forward-chaining.
;;;

(defun apply-ruleset-to-case (c rs-name)
  (let ((rs (ruleset rs-name))
	(enhanced-case c))
    (with-ruleset-array 
     rs
     (dolist (r-name ruleset-rules)
       (let ((result 
	      (apply-rule-array 
	       (rule r-name)
	       enhanced-case)))
	 (when (not (equal result enhanced-case))
	   (setq enhanced-case result)))))
    enhanced-case))

;;;
;;; VERIFY-RULESET: Given a ruleset name, attempt to verify all of its
;;;  associated rules.
;;;

(defun verify-ruleset (rs-name)
  (let ((rs (ruleset rs-name)))
    (with-ruleset-array 
     rs
     (dolist (r-name ruleset-rules)
       (verify-rule r-name)))))

;;;
;;; DEFRULE: Define a rule and add its corresponding rule-array to
;;;  *RULES-TABLE*.
;;;

(defmacro defrule (name &key conclusion hypotheses)
  (setf (gethash name *rules-table*) 
	(make-rule
	 :name name
	 :conclusion conclusion
	 :hypotheses hypotheses))
  `(quote ,name))

;;;
;;; DEFRULESET: A macro for defining rulesets.
;;;  :verified? can be either T, NIL, or SYSTEM.
;;;  SYSTEM means that the ruleset is part of the core
;;;   RAHD distribution (e.g., it's been verified by
;;;   me, Grant, using VERIFY-RULESET, and we thus
;;;   mark it as verified a priori when building RAHD).
;;;

(defmacro defruleset (name &key hvlevel verified? active? rules)
  (setf (gethash name *rule-sets-table*)
	(make-ruleset
	 :name name
	 :rules rules
	 :hvlevel hvlevel
	 :verified? verified?
	 :active? active?))
  `(quote ,name))
  
;;;
;;; ACTIVATE-RULE-IN-RULESET: Mark a rule as active in a given
;;;  ruleset.
;;;

(defun activate-rule-in-ruleset (r-name rs-name)
  (let ((r (rule r-name))
	(rs (ruleset rs-name)))
    (with-rule-array 
     r
     (with-ruleset-array
      rs
      (setf (aref r 6) (union (list rs-name) rule-rulesets))
      (when (not (equal rule-active? t))
	(setf (aref r 7) (union (list rs-name) rule-active?)))
      (when (not (equal ruleset-active? t))
	(setf (aref rs 4) (union (list r-name) ruleset-active?)))
      (when (not (member r-name ruleset-rules))
	(setf (aref rs 1) (union (list r-name) ruleset-rules))))))
  (fmt 0 "~% Activated rule ~A in ruleset ~A.~%~%" r-name rs-name))

;;;
;;; RULE: Given a rule name (a symbol), return the associated
;;;  rule-array by looking it up in *rules-table*.
;;;

(defun rule (name)
  (gethash name *rules-table*))

;;;
;;; RULESET: Given a ruleset name (a symbol), return the associated
;;;  rule-set-array by looking it up in *rule-sets-table*.
;;;

(defun ruleset (name)
  (gethash name *rule-sets-table*))

;;;
;;; PRINT-RULE: Given a rule name (a symbol), print it.
;;;

(defun print-rule (name)
  (print-rule-array (rule name)))

;;;
;;; PRINT-RULESET: Given a ruleset name (a symbol), print it.
;;;

(defun print-ruleset (name)
  (print-ruleset-array (ruleset name)))

;;;
;;; VERIFY-RULE: Given a rule name (a symbol), verify the rule.
;;;

(defun verify-rule (name)
  (verify-rule-array (rule name)))

;;;
;;; ALL-RULES: Print a list of all known rules.
;;;

(defun all-rules ()
  (fmt 0 "~%-{Defined rules}------------------------------------------------------~%")
  (maphash #'(lambda (x y)
	       (declare (ignore x))
	       (with-rule-array 
		y
		(fmt 0 " Name:      ~A\
 Verified?: ~A\
 Active?:   ~A\
----------------------------------------------------------------------~%" 
		     rule-name
		     rule-verified?
		     rule-active?))) *rules-table*)
  (fmt 0 " * For information on a rule, use (print-rule 'rule-name).~%~%"))

;;;
;;; ALL-RULES: Print a list of all known rules.
;;;

(defun all-rulesets ()
  (fmt 0 "~%-{Defined rulesets}---------------------------------------------------~%")
  (maphash #'(lambda (x y)
	       (declare (ignore x))
	       (with-ruleset-array 
		y
		(fmt 0 " Name:      ~A\
 Verified?: ~A\
 Rules:     ~A\
 Active?:   ~A\
----------------------------------------------------------------------~%" 
		     ruleset-name
		     ruleset-verified?
		     ruleset-rules
		     ruleset-active?))) *rule-sets-table*)
  (fmt 0 " * For information on a ruleset, use (print-ruleset 'ruleset-name).~%~%"))

(defun show-rules () (all-rules))
(defun show-rulesets () (all-rulesets))
(defun print-rules () (all-rules))
(defun print-rulesets () (all-rulesets))

;;;
;;; RULESET-ENABLED?: Is a given ruleset currently enabled?
;;;

(defun ruleset-enabled? (ruleset-name)
  t)

;;;
;;; MAKE-RULE: Make a rule array.
;;;

(defun make-rule (&key name hvlevel conclusion hypotheses
		       verified? proof-tr active? rulesets)
  (cond ((not (and (consp conclusion)
		   (= (length conclusion) 1)))
	 (break "Conclusions of RAHD rules must consist of a single conjunct."))
	(t (make-array '(8) :initial-contents
		       `(,name
			 ,hvlevel
			 ,conclusion
			 ,hypotheses
			 ,verified?
			 ,proof-tr
			 ,active?
			 ,rulesets)))))

;;;
;;; MAKE-RULESET: Make a ruleset array.
;;;
;;;  VERIFIED? is either T, NIL, SYSTEM, or a list of rules
;;;    in the ruleset which have been verified.
;;;    T means all rules in the ruleset have been verified.
;;;    NIL means none of the rules in the ruleset have been v'd.
;;;    SYSTEM means we'll act as if all rules were v'd.
;;;  ACTIVE? is either T, NIL, or a list of rules in the ruleset
;;;    which are active.
;;;

(defun make-ruleset (&key name rules hvlevel verified? active?)
  (make-array '(5) :initial-contents
	      `(,name
		,rules
		,hvlevel
		,verified?
		,active?)))

;;;
;;; WITH-RULE-ARRAY: A simple macro deconstructing a rule array.
;;;

(defmacro with-rule-array (r &rest rst)
  `(let ((rule-name (aref ,r 0))
	 (rule-hvlevel (aref ,r 1))
	 (rule-conclusion (aref ,r 2))
	 (rule-hypotheses (aref ,r 3))
	 (rule-verified? (aref ,r 4))
	 (rule-proof-tr (aref ,r 5))
	 (rule-active? (aref ,r 6))
	 (rule-rulesets (aref ,r 7)))
     (declare (ignorable rule-name
			 rule-hvlevel
			 rule-conclusion
			 rule-hypotheses
			 rule-verified?
			 rule-proof-tr
			 rule-active?
			 rule-rulesets))
     ,@rst))

;;;
;;; WITH-RULESET-ARRAY: A simple macro deconstructing a ruleset array.
;;;

(defmacro with-ruleset-array (r &rest rst)
  `(let ((ruleset-name (aref ,r 0))
	 (ruleset-rules (aref ,r 1))
	 (ruleset-hvlevel (aref ,r 2))
	 (ruleset-verified? (aref ,r 3))
	 (ruleset-active? (aref ,r 4)))
     (declare (ignorable ruleset-name
			 ruleset-rules
			 ruleset-hvlevel
			 ruleset-verified?
			 ruleset-active?))
     ,@rst))

;;;
;;; PRINT-RULE-ARRAY: Pretty print a rule array.
;;;

(defun print-rule-array (r)
  (with-rule-array 
   r
   (fmt 0
	"~%\
-{Rule record}--------------------------------------------------------\
 Name:       ~A\
 HVLevel:    ~A\
 Conclusion: ~A\
 Hypotheses: ~A\
 Verified?:  ~A\
 Proof TR:   ~A\
 Active?:    ~A\
 Rulesets:   ~A\
----------------------------------------------------------------------~%~%"
	rule-name rule-hvlevel rule-conclusion rule-hypotheses
	rule-verified? rule-proof-tr rule-active? rule-rulesets))
  t)

;;;
;;; PRINT-RULESET-ARRAY: Pretty print a ruleset array.
;;;

(defun print-ruleset-array (r)
  (with-ruleset-array 
   r
   (fmt 0
	"~%\
-{Ruleset record}-----------------------------------------------------\
 Name:       ~A\
 HVLevel:    ~A\
 Rules:      ~A\
 Verified?:  ~A\
 Active?:    ~A\
----------------------------------------------------------------------~%~%"
	ruleset-name ruleset-hvlevel ruleset-rules
	ruleset-verified? ruleset-active?))
  t)

;;;
;;; VERIFY-RULE-ARRAY: Given a rule array, try to verify the rule.
;;;  Note: Presently we just use TRY-TO-PROVE.
;;;

(defun verify-rule-array (r)
  (with-rule-array 
   r
   (let ((goal-to-verify 
	  (mapcar #'(lambda (x) (list x))
		  (append rule-hypotheses 
			  `((NOT ,(car rule-conclusion)))))))
     (fmt 0 "~%-{Rule verification}--------------------------------------------------\
 Verifying rule: ~A,~% Associated goal: ~A.~%~%" 
	  rule-name goal-to-verify)
     (let ((result (try-to-prove
			   goal-to-verify
			   'rule-verification)))
       (if result
	   (progn 
	     (setf (aref r 4) t)
	     (setf (aref r 5) (tr))
	     (fmt 0 "~% .:. Rule verified.~%"))
	 (fmt 0 "~% Rule not verified.~%"))
       (fmt 0 "----------------------------------------------------------------------~%~%")
       result))))

;;;
;;; RULE-IMPL: Given a rule array, return a simple implicational formula
;;;  of the form (IMPLIES (AND HYP_1 ... HYP_n) CONC).
;;;

(defun rule-impl (r)
  (with-rule-array 
   r
   `(IMPLIES (AND ,@rule-hypotheses) ,@rule-conclusion)))

;;;
;;; APPLY-RULE-ARRAY: Given a case and a rule array, attempt to apply
;;;  the rule to the case.  We use a very simple perfect matching
;;;  scheme to see if rule hypotheses are relieved.
;;;

(defun apply-rule-array (r c)
  (with-rule-array 
   r
   (multiple-value-bind 
       (fresh-r-bindings fresh-impl-r)
       (fresh-vars-r (rule-impl r))
     (let ((fresh-rule-hypotheses
	    (cdadr fresh-impl-r))
	   (fresh-rule-conclusion
	    (cddr fresh-impl-r))
	   (forall-vars
	    (let ((favs nil))
	      (mapcar #'(lambda (x)
			  (setq favs (cons (cdr x) favs)))
		      fresh-r-bindings)
	      favs)))
       (let ((validated-substs-hash (make-hash-table :test 'eq))
	     (validated-substs nil))

	 (satisfy-hyps 
	  fresh-rule-hypotheses
	  c 
	  validated-substs-hash
	  nil
	  forall-vars)
	  
	 (maphash #'(lambda (x y) 
		      (declare (ignore x))
		      (setq validated-substs
			    (cons y validated-substs)))
		  validated-substs-hash)
	 ;;
	 ;; So, now validated-substs is a list of all validated
	 ;; substitutions.
	 ;;
	 ;; Let's add the corresponding instantiations of the
	 ;; rule-conclusion to C and return them!
	 ;;

	 (when validated-substs
	   (fmt 2.5 "~%")
	   (dolist (s validated-substs)
	     (let ((conclusion-instance
		    (apply-bindings (car fresh-rule-conclusion) s)))
	     (fmt 2.5 "~% Forward-chaining with rule ~A:\
   Conclusion instance: ~A.~%" rule-name conclusion-instance)
	     (setq c (cons conclusion-instance c))))
	   (fmt 2.5 "~%"))
	     
	 c)))))

;;;
;;; SATISFY-HYPS: Given a rule hypothesis list, which is itself
;;;  an implicitly conjoined list of single hypotheses, check
;;;  to make sure that every rule hypothesis is satisfied in
;;;  a given case C.  If we find a substitution that makes
;;;  every hypothesis satisfied in C, then we add it to our 
;;;  hash-table.  In the end, the hash-table will contain every
;;;  validated substitution.
;;;
;;; We modify validated-substs-hash, populating it with entries
;;;  of the form: (KEY=instance_id VALUE=validated_subst).
;;;
;;; Instance_ID's are given by GENSYM.
;;;

(defun satisfy-hyps (hyps c validated-substs-hash cur-bindings forall-vars)
  (cond ((endp hyps) (setf (gethash (gensym) validated-substs-hash)
			   cur-bindings))
	(t (let ((top-hyp (car hyps)))
	     (let ((substs-for-top-hyp
		    (find-hyp-case-matches top-hyp c forall-vars)))
	       (dolist (s substs-for-top-hyp)
		 (let ((updated-hyps 
			(mapcar #'(lambda (x) (apply-bindings x s)) 
				(cdr hyps))))
		   (satisfy-hyps 
		    updated-hyps 
		    c 
		    validated-substs-hash
		    (append s cur-bindings) 
		    forall-vars))))))))

;;;
;;; FIND-HYP-CASE-MATCHES: 
;;;  Given a single hypothesis literal, a case, and a list of
;;;  forall-vars, return a list of list of bindings of forall-
;;;  vars corresponding to all matches of HYP with lits in C.
;;;
;;; Note that returning (NIL) means that the empty substitution
;;;  yields a match between HYP and a member of C.  
;;; Returning NIL means that no match exists.
;;;

(defun find-hyp-case-matches (hyp c forall-vars)
  (let ((bindings-lst nil))
    (dolist (l c)
      (multiple-value-bind
	  (match? bindings)
	  (match-rule-hyp-to-lit 
	   hyp 
	   l 
	   :forall-vars forall-vars)
	(when match?
	  (setq bindings-lst (cons bindings bindings-lst)))))
  bindings-lst))

;;;
;;; MATCH-RULE-HYP-TO-LIT: Given a rule hypothesis and a literal,
;;;  attempt to find a perfect match (instantiation of rule hyp
;;;  variables making a perfect match to the (ground) literal.
;;;
;;; But, we incorporate some simple generalisations:
;;;  If H is (>= X Y) and L is either (> X Y) or (= X Y),
;;;   then this is allowed to be a match, and so on.
;;;
;;; We return a form of the species:
;;;   (values SUCCESS? ((V_0 C_0) (V_1 C_1) ... (V_k C_k))),
;;;  V_i are (passed-in fresh) rule-hyp variables, 
;;;  and C_i are literal variables (ground).
;;;

(defun match-rule-hyp-to-lit (h l &key forall-vars)
  (let ((op-h (car h))
	(op-l (car l))
	(x-h (cadr h))
	(x-l (cadr l))
	(y-h (caddr h))
	(y-l (caddr l)))
    (multiple-value-bind 
	(tm-success? bindings-h->l)
	(match-terms x-h x-l y-h y-l :forall-vars forall-vars)
      (let ((result
	     (when tm-success?
	       (case op-h
		 (>= (case op-l
		       ((> = >=) tm-success?)))
		 (> (case op-l
		      (> tm-success?)))
		 (= (case op-l
		      (= tm-success?)))
		 (< (case op-l
		      (< tm-success?)))
		 (<= (case op-l
		       ((< = <=) tm-success?)))))))
	(if result
	    (values t bindings-h->l)
	  (values nil nil))))))

;;;
;;; MATCH-TERMS: Given X-H, Y-H hypothesis terms and 
;;;   X-L, Y-L literal terms, attempt to match them
;;;   by instantiating the hypothesis terms.
;;;
;;; Note, we now take a keyword parameter:
;;;  FORALL-VARS.
;;; If this is non-nill, then we will only allow
;;;  vars appearing in this list to be instantiated.
;;; This is used when trying to build HYP instantiations,
;;;  as some universal vars may have been substituted
;;;  with implicitly existentially quantified variables,
;;;  and we need to keep track of which is which.
;;;
;;; We return:
;;;  (values SUCCESS? BINDINGS(TM-H->TM-L)).
;;;

(defun match-terms (x-h x-l y-h y-l &key forall-vars)
  (let ((tm-h `(- ,x-h ,y-h))
	(tm-l `(- ,x-l ,y-l))
	(b-hash (make-hash-table :test 'eq)))
    (let ((b nil))
      (match-terms* tm-h tm-l b-hash :forall-vars forall-vars)
      (maphash #'(lambda (x y)
		   (setq b (cons (cons x y) b))) b-hash)
      (let ((instance (apply-bindings tm-h b)))
	(if (equal instance tm-l)
	    (values t b)
	  (values nil nil))))))

(defun match-terms* (tm-h tm-l b-hash &key forall-vars)
  (cond ((or (equal tm-h nil)
	     (equal tm-l nil)) nil)
	((and (symbolp tm-h)
	      (if forall-vars (member tm-h forall-vars) t))
	 (multiple-value-bind
	     (binding exists?)
	     (gethash tm-h b-hash)
	   (declare (ignore binding))
	   (when (not exists?)
	     (setf (gethash tm-h b-hash) tm-l))))
	((and (consp tm-h)
	      (consp tm-l)
	      (equal (car tm-h) (car tm-l)))
	 (match-terms* (cadr tm-h) (cadr tm-l) b-hash :forall-vars forall-vars)
	 (match-terms* (caddr tm-h) (caddr tm-l) b-hash :forall-vars forall-vars))))

;;; 
;;; FRESH-VARS-R:
;;; Given a rule with implicitly universally quantified
;;;  variables, return a list of bindings of its variables 
;;;  to fresh variables which are guaranteed not to clash 
;;;  with any of the names for implicitly existentially 
;;;  quantified RAHD constants (e.g., those in RAHD formulae), 
;;;  together with a variant of r obtained via the substitution.
;;;
;;;  So, we return (values fresh-bindings fresh-r).
;;;

(defun fresh-vars-r (r)
  (let ((b-hash (make-hash-table :test 'eq))
	(b nil))
    (fresh-vars-r* r b-hash)
    (maphash #'(lambda (x y) 
		 (setq b (cons (cons x y) b))) b-hash)
    (values b (apply-bindings r b))))

(defun fresh-vars-r* (r b-hash)
  (cond ((symbolp r) (multiple-value-bind 
			 (fresh-sym exists?)
			 (gethash r b-hash)
		       (declare (ignore fresh-sym))
		       (when (not exists?)
			 (setf (gethash r b-hash) 
			       (gensym)))))
	((consp r) 
	 (fresh-vars-r* (cadr r) b-hash)
	 (fresh-vars-r* (caddr r) b-hash))))

;;;
;;; APPLY-BINDINGS:
;;; Given an implicitly universally quantified formula
;;;  and a list of bindings ((V_i . T_i)), return the
;;;  result of applying the substitutions V_i->T-i to F.
;;;

(defun apply-bindings (f bindings)
  (let ((out f))
    (dolist (b bindings)
      (setq out (subst (cdr b) (car b) out)))
    out))