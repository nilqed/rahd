;;;
;;; An utterly disorganised scratch-sheet of personal RAHD notes.
;;;  g.o.passmore (2008-2011)
;;;

(g '(((>= A 0)) ((>= B 0)) ((>= C 0)) ((>= D 0)) ((>= E 0)) ((>= F 0))
     ((>= G 0)) ((<= A 1)) ((<= B 1)) ((<= C 1)) ((<= D 1)) ((<= E 1))
     ((<= F 1)) ((<= G 1)) ((= (+ (* E E E F F F) G -2) 0))
     ((= (+ (* F F F F) G) (+ G 1)))
     ((= (+ (* 2 G G G G G) (* F F G) (- 0 G)) 0))
     ((< (* (+ F G) (+ F G)
	    (+ (* (- 1 (* A A B B)) (- 1 (* C D)) (- (* A D) (* B C))
		  (- (* A D) (* B C)))
	       (* (* 2 A B) (- (* C D) (* A B)) (- 1 (* A B)) (- C D)
		  (- C D))
	       (* (- (* A A B B) (* C C D D)) (- 1 (* C D)) (- A B)
		  (- A B))))
	 0)
      (= (* (+ 2 F G) (+ G 11)) A))) )


Case 191 before any manipulations (arrived at with e1 [run calculemus-0] from goal 0):

   191     ((<= B 1) (<= C 1) (<= D 1) (<= E 1) (<= F 1) (<= G 1)
              (= (+ (* E (* E (* E (* F (* F F))))) (+ G -2)) 0)
              (= (+ (* F (* F (* F F))) G) (+ G 1))
              (= (+ (* 2 (* G (* G (* G (* G G))))) (+ (* F (* F G)) (- 0 G)))
                 0)
              (<
               (* (+ F G)
                  (* (+ F G)
                     (+
                      (* (- 1 (* A (* A (* B B))))
                         (* (- 1 (* C D))
                            (* (- (* A D) (* B C)) (- (* A D) (* B C)))))
                      (+
                       (* (* 2 (* A B))
                          (* (- (* C D) (* A B))
                             (* (- 1 (* A B)) (* (- C D) (- C D)))))
                       (* (- (* A (* A (* B B))) (* C (* C (* D D))))
                          (* (- 1 (* C D)) (* (- A B) (- A B))))))))
               0)
              (> A 0) (> B 0) (> C 0) (> D 0) (> E 0) (> F 0) (= G 0) (< A 1))    (UNKNOWN)

To install:

(g (mapcar #'list '((<= B 1) (<= C 1) (<= D 1) (<= E 1) (<= F 1) (<= G 1)
              (= (+ (* E (* E (* E (* F (* F F))))) (+ G -2)) 0)
              (= (+ (* F (* F (* F F))) G) (+ G 1))
              (= (+ (* 2 (* G (* G (* G (* G G))))) (+ (* F (* F G)) (- 0 G)))
                 0)
              (<
               (* (+ F G)
                  (* (+ F G)
                     (+
                      (* (- 1 (* A (* A (* B B))))
                         (* (- 1 (* C D))
                            (* (- (* A D) (* B C)) (- (* A D) (* B C)))))
                      (+
                       (* (* 2 (* A B))
                          (* (- (* C D) (* A B))
                             (* (- 1 (* A B)) (* (- C D) (- C D)))))
                       (* (- (* A (* A (* B B))) (* C (* C (* D D))))
                          (* (- 1 (* C D)) (* (- A B) (- A B))))))))
               0)
              (> A 0) (> B 0) (> C 0) (> D 0) (> E 0) (> F 0) (= G 0) (< A 1))))


*** Before applying RCR-INEQS but after the other previous CMFs:

       0     ((<= B 1) (<= C 1) (<= D 1) (<= E 1) (<= F 1)
              (= (+ (* (* F (* F F)) (* E (* E E))) -2) 0)
              (= (+ (* F (* F (* F F))) -1) 0)
              (<
               (+
                (* (* B B)
                   (* (* D (* D D)) (* (* F F) (* (* A (* A (* A A))) C))))
                (+
                 (* -2
                    (* (* B (* B B))
                       (* (* D D) (* (* F F) (* (* A (* A A)) (* C C))))))
                 (+
                  (* (* B (* B (* B B)))
                     (* D (* (* F F) (* (* A A) (* C (* C C))))))
                  (+ (* (* D (* D D)) (* (* F F) (* (* A A) (* C (* C C)))))
                     (+
                      (* -2
                         (* B
                            (* (* D (* D D)) (* (* F F) (* A (* C (* C C)))))))
                      (+
                       (* -2
                          (* (* B B)
                             (* D (* (* F F) (* (* A A) (* C (* C C)))))))
                       (+
                        (* -1
                           (* (* B B)
                              (* D (* (* F F) (* (* A (* A (* A A))) C)))))
                        (+
                         (* 4
                            (* (* B B)
                               (* (* D D) (* (* F F) (* (* A A) (* C C))))))
                         (+
                          (* -1
                             (* (* B B)
                                (* (* D D) (* (* F F) (* A (* A (* A A)))))))
                          (+
                           (* (* B B)
                              (* (* D (* D D)) (* (* F F) (* C (* C C)))))
                           (+
                            (* -2
                               (* (* B B)
                                  (* (* D (* D D)) (* (* F F) (* (* A A) C)))))
                            (+
                             (* 2
                                (* (* B (* B B))
                                   (* (* F F) (* (* A (* A A)) (* C C)))))
                             (+
                              (* 2
                                 (* (* B (* B B))
                                    (* (* D D) (* (* F F) (* A (* A A))))))
                              (+
                               (* -1
                                  (* (* B (* B (* B B)))
                                     (* (* F F) (* (* A A) (* C C)))))
                               (+
                                (* -1
                                   (* (* B (* B (* B B)))
                                      (* D (* (* F F) (* (* A A) C)))))
                                (+
                                 (* -1
                                    (* (* D D)
                                       (* (* F F) (* (* A A) (* C C)))))
                                 (+
                                  (* -1
                                     (* (* D (* D D))
                                        (* (* F F) (* (* A A) C))))
                                  (+
                                   (* 2
                                      (* B
                                         (* D
                                            (* (* F F) (* A (* C (* C C)))))))
                                   (+
                                    (* 2
                                       (* B
                                          (* (* D (* D D))
                                             (* (* F F) (* A C)))))
                                    (+
                                     (* -2
                                        (* (* B B)
                                           (* (* F F) (* (* A A) (* C C)))))
                                     (+
                                      (* (* B B)
                                         (* (* F F) (* A (* A (* A A)))))
                                      (+
                                       (* -1
                                          (* (* B B)
                                             (* D (* (* F F) (* C (* C C))))))
                                       (+
                                        (* 4
                                           (* (* B B)
                                              (* D (* (* F F) (* (* A A) C)))))
                                        (+
                                         (* -1
                                            (* (* B B)
                                               (* (* D D)
                                                  (* (* F F) (* C C)))))
                                         (+
                                          (* -2
                                             (* (* B B)
                                                (* (* D D)
                                                   (* (* F F) (* A A)))))
                                          (+
                                           (* -2
                                              (* (* B (* B B))
                                                 (* (* F F) (* A (* A A)))))
                                           (+
                                            (* (* B (* B (* B B)))
                                               (* (* F F) (* A A)))
                                            (+ (* (* D D) (* (* F F) (* A A)))
                                               (+
                                                (* -2
                                                   (* B
                                                      (* D
                                                         (* (* F F) (* A C)))))
                                                (* (* B B)
                                                   (* (* F F)
                                                      (* C
                                                         C))))))))))))))))))))))))))))))))
               0)
              (> A 0) (> B 0) (> C 0) (> D 0) (> E 0) (> F 0) (< A 1))    (UNKNOWN
                                                                           CANON-TMS
                                                                           SIMP-GLS
                                                                           SIMP-ARITH
                                                                           SIMP-GLS
                                                                           DEMOD-NUM
                                                                           SIMP-ZRHS) 


Case 191 where SAT is found:
 (SAT QEPCAD RCR-INEQS CANON-TMS SATUR-LIN SIMP-GLS
      SIMP-ARITH SIMP-GLS DEMOD-NUM SIMP-ZRHS).



;;; Strange results on this problem:

Case 191 from goal 0.0:

(g (mapcar #'list
 '((<
               (+
                (* (* A A)
                   (* D (* (* C (* C C)) (* (* B (* B (* B B))) (* F F)))))
                (+
                 (* -2
                    (* (* A (* A A))
                       (* (* D D) (* (* C C) (* (* B (* B B)) (* F F))))))
                 (+
                  (* (* A (* A (* A A)))
                     (* (* D (* D D)) (* C (* (* B B) (* F F)))))
                  (+ (* (* D (* D D)) (* (* C (* C C)) (* (* B B) (* F F))))
                     (+
                      (* -2
                         (* A
                            (* (* D (* D D)) (* (* C (* C C)) (* B (* F F))))))
                      (+
                       (* -1
                          (* (* A A)
                             (* (* C C) (* (* B (* B (* B B))) (* F F)))))
                       (+
                        (* -1
                           (* (* A A)
                              (* D (* C (* (* B (* B (* B B))) (* F F))))))
                        (+
                         (* -2
                            (* (* A A)
                               (* D (* (* C (* C C)) (* (* B B) (* F F))))))
                         (+
                          (* 4
                             (* (* A A)
                                (* (* D D) (* (* C C) (* (* B B) (* F F))))))
                          (+
                           (* -2
                              (* (* A A)
                                 (* (* D (* D D)) (* C (* (* B B) (* F F))))))
                           (+
                            (* (* A A)
                               (* (* D (* D D)) (* (* C (* C C)) (* F F))))
                            (+
                             (* 2
                                (* (* A (* A A))
                                   (* (* C C) (* (* B (* B B)) (* F F)))))
                             (+
                              (* 2
                                 (* (* A (* A A))
                                    (* (* D D) (* (* B (* B B)) (* F F)))))
                              (+
                               (* -1
                                  (* (* A (* A (* A A)))
                                     (* D (* C (* (* B B) (* F F))))))
                               (+
                                (* -1
                                   (* (* A (* A (* A A)))
                                      (* (* D D) (* (* B B) (* F F)))))
                                (+
                                 (* -1
                                    (* D
                                       (* (* C (* C C)) (* (* B B) (* F F)))))
                                 (+
                                  (* -1
                                     (* (* D D)
                                        (* (* C C) (* (* B B) (* F F)))))
                                  (+
                                   (* 2
                                      (* A
                                         (* D
                                            (* (* C (* C C)) (* B (* F F))))))
                                   (+
                                    (* 2
                                       (* A
                                          (* (* D (* D D))
                                             (* C (* B (* F F))))))
                                    (+
                                     (* (* A A)
                                        (* (* B (* B (* B B))) (* F F)))
                                     (+
                                      (* -2
                                         (* (* A A)
                                            (* (* C C) (* (* B B) (* F F)))))
                                      (+
                                       (* 4
                                          (* (* A A)
                                             (* D (* C (* (* B B) (* F F))))))
                                       (+
                                        (* -2
                                           (* (* A A)
                                              (* (* D D) (* (* B B) (* F F)))))
                                        (+
                                         (* -1
                                            (* (* A A)
                                               (* (* D D)
                                                  (* (* C C) (* F F)))))
                                         (+
                                          (* -1
                                             (* (* A A)
                                                (* (* D (* D D))
                                                   (* C (* F F)))))
                                          (+
                                           (* -2
                                              (* (* A (* A A))
                                                 (* (* B (* B B)) (* F F))))
                                           (+
                                            (* (* A (* A (* A A)))
                                               (* (* B B) (* F F)))
                                            (+ (* (* C C) (* (* B B) (* F F)))
                                               (+
                                                (* -2
                                                   (* A
                                                      (* D
                                                         (* C (* B (* F F))))))
                                                (* (* A A)
                                                   (* (* D D)
                                                      (* F
                                                         F))))))))))))))))))))))))))))))))
               0)
              (= (+ (* F (* F (* F F))) -1) 0)
              (= (+ (* (* E (* E E)) (* F (* F F))) -2) 0) (< A 1) (> F 0)
              (> E 0) (> D 0) (> C 0) (> B 0) (> A 0) (<= F 1) (<= E 1)
              (<= D 1) (<= C 1) (<= B 1)) ))

(g '(((>= A 0)) ((>= B 0)) ((>= C 0)) ((>= D 0)) ((>= E 0)) ((>= F 0))
    ((>= G 0)) ((<= A 1)) ((<= B 1)) ((<= C 1)) ((<= D 1)) ((<= E 1))
    ((<= F 1)) ((<= G 1)) ((= (+ (* E E E F F F) G -2) 0))
    ((= (+ (* F F F F) G) (+ G 1)))
    ((= (+ (* 2 G G G G G) (* F F G) (- 0 G)) 0))
    ((< (* (+ F G) (+ F G)
           (+ (* (- 1 (* A A B B)) (- 1 (* C D)) (- (* A D) (* B C))
                 (- (* A D) (* B C)))
              (* (* 2 A B) (- (* C D) (* A B)) (- 1 (* A B)) (- C D)
                 (- C D))
              (* (- (* A A B B) (* C C D D)) (- 1 (* C D)) (- A B)
                 (- A B))))
        0)
     (= (* (+ 2 F G) (+ G 11)) A))))

(build-gs :do-not-split-ineqs? t)


(r)
(g (mapcar #'list '((= (+ (* E (* E (* E (* F (* F F))))) (+ G -2)) 0)
              (= (+ (* F (* F (* F F))) G) (+ G 1))
              (= (+ (* 2 (* G (* G (* G (* G G))))) (+ (* F (* F G)) (- 0 G)))
                 0)
              (<
               (* (+ F G)
                  (* (+ F G)
                     (+
                      (* (- 1 (* A (* A (* B B))))
                         (* (- 1 (* C D))
                            (* (- (* A D) (* B C)) (- (* A D) (* B C)))))
                      (+
                       (* (* 2 (* A B))
                          (* (- (* C D) (* A B))
                             (* (- 1 (* A B)) (* (- C D) (- C D)))))
                       (* (- (* A (* A (* B B))) (* C (* C (* D D))))
                          (* (- 1 (* C D)) (* (- A B) (- A B))))))))
               0)
              (> A 0) (> B 0) (> C 0) (> D 0) (> E 0) (> F 0) (= G 0) (< A 1)
              (= B 1) (= C 1) (= D 1) (= E 1) (= F 1) (= G 1))
))
(build-gs :do-not-split-ineqs? t)


Working on a problem from Munoz via Paulson:

--
vars x1 x2 x3 x4 x5 x6 x7 x8
assert -0.1 <= x1 /\ x1 <= 0.4
assert -1/10 <= x1 /\ x1 <= 4/10
assert 4/10 <= x2 /\ x2 <= 1
assert -7/10 <= x3 /\ x3 <= -4/10
assert -7/10 <= x4 /\ x4 <= 4/10
assert 1/10 <= x5 /\ x5 <= 2/10
assert -1/10 <= x6 /\ x6 <= 6/10
assert -3/10 <= x7 /\ x7 <= 11/10
assert -11/10 <= x8 /\ x8 <= -3/10
assert (0 - x1)*x6^3 + 3*x1*x6*x7^2 - x3*x7^3 + 3*x3*x7*x6^2 - x2*x5^3 + 3*x2*x5*x8^2 - x4*x8^3 + 3*x4*x8*x5^2 < -17435/10000
--

build-gs
e [split-ineqs; demod-lin; run stable-simp; interval-cp; if (dim<=2) fdep-cad contra-eqs]
lisp (swap-to-goal '(0 0))
e [canon-tms; interval-cp]
e [when (dim=3) [qepcad(open? := 1)]]
e [when (dim=4) [qepcad(open? := 1)]]

e1 [split-ineqs; cg(goal := 0.0); demod-lin; 
    run-stable-simp; interval-cp;
    when (dim <= 2) fdep-cad(factor? := 1);
    canon-tms; interval-cp;
    when (dim <= 4) qepcad(open? := 1);
   ]

;;;
;;; a hilariously verbose example showing all interactive style
;;;  of proving a simple theorem (we could have proved it directly
;;;  just with bounded-gbrni :-) but this is fun to imagine what
;;;  eventual RAHD proof scripts might look like in the vain of Coq style.
;;;  (The proof itself runs in RAHD now, but if we ever did things in
;;;   this style we'd make the syntax cleaner.)
;;;

Theorem ex1 Empty({x,y,z : R | x >= y /\ y >= z /\ z > x}).
Proof:
 e1 [split-ineqs(atom := 0)]
 lisp (swap-to-goal '(0 0))
 e [demod-lin]
 e [run stable-simp]
 e1 split-ineqs(atom := 1)
 lisp (swap-to-goal '((0 0) 0))
 e1 [split-ineqs(atom := 0)]
 lisp (swap-to-goal '(((0 0) 0) 0))
 e [demod-lin; run stable-simp; bounded-gbrni]
 up 
 up
 lisp (swap-to-goal '((0 0) 1))
 e split-ineqs(atom := 0)
 lisp (swap-to-goal '(((0 0) 1) 0)))
 e [demod-lin]
 e [run stable-simp]
 e [bounded-gbrni]
 up 
 up
 up
Qed.


;;; Thoughts on strategy language.
;;;
;;; > stage0 =s= { intervalcp; gbpsatz; fdepcad }
;;; > stage1 =s= { ... ... }
;;; > waterfall =s= { stage0; explode-ineqs then stage1 }
;;; > check with waterfall
;;;
;;; also want || for threading.
;;; idea: 
;;;       x || y means do both x and y and kill one if the
;;;               other finishes, return the result of the
;;;               first one that finished and ignore rest. 
;;;
;;; > cost-intervalcp =c= { num-vars^2 + num-literals }
;;; > assign-cost cost-intervalcp to intervalcp
;;;
;;; > my-simp-ordinal =o= <num-vars, num-literals, total-degree>
;;; > my-cmf-pool =p= { intervalcp, gbpsatz, fdepcad }
;;; > check with my-cmf-pool via best-first guided-by my-simp-ordinal
;;;

;;;
;;; s0 =s= {   { simp-zrhs ; stable-simp ; interval-cp ; gb-psatz } 
;;;         || { qepcad } 
;;;         || { redlog } 
;;;         || { sos } 
;;;        }
;;;


;;;
;;; Doesn't print out full model:
;;;

s001:..Code/rahd > ./rahd-v0.6-lx32 -formula "(((>= pK 0)) 
     ((<= pK 1))
     ((>= pL 0))
     ((<= pL 1))
    ((> (/ (+ (* 1 pK pK pK pK pK pK pL pL pL pL pL pL)
       (* -6 pK pK pK pK pK pL pL pL pL pL)
      (* 15 pK pK pK pK pL pL pL pL)
      (* -18 pK pK pK pL pL pL)
      (* 9 pK pK pL pL) -1) pL)
        -8)) ((= x 1)) ((= y 2)))" -verbosity 0  -print-model 

 sat
 model: [PL=1,
         X=1,
         PK=0].

;;;
;;; Good CAD versus partial CAD example for my thesis:
;;;  (takes ~60 sec to find satisfying vector when full, but only ~13 when partial).
;;;

(wrv 3 (fd-cad-sat? '((> (* U1 R1) 1)
 (> (* U1 X1) (* U1 U3))
 (< (* U3 R3) 1)
 (< (* U3 X2) (* (- U2 U1) X1))
 (> (* U3 X4) (* U2 X3))
 (< (* X1 X4)
    (- (* (- X2 U1) X3) (* U1 X1)))
 (> (* (+ (* 2 (* U2 X4))
	  (- (- (* 2 (* U3 X3)) (* U3 U3))
	     (* U2 U2)))
       R1) 0)) :partial? nil))

;;;
;;; RRS(2):
;;;

* (p)

 Printing all of the remaining 1 cases for goal 0.

 -------     -------------------------------------------------------------------
 case-id     case
 -------     -------------------------------------------------------------------

       0     ((= (+ (* B1 A1) (* B2 A2)) 0)
              (=
               (+ (* A1 A1)
                  (+ (* A2 A2) (+ (* -1 (* B1 B1)) (+ (* -1 (* B2 B2)) -2))))
               0)
              (< (+ (* A2 A1) (* -1 (* B2 B1))) 0) (> A2 0) (> A1 0))    (UNKNOWN
                                                                          SIMP-ZRHS
                                                                          SATUR-LIN
                                                                          CANON-TMS) 

But, if we use simple inequality chaining/squeezing, and obtain:

(g '(((= (+ (* B1 A1) (* B2 A2)) 0))
     ((= (+ (* A1 A1) (+ (* A2 A2) (+ (* -1 (* B1 B1)) (+ (* -1 (* B2 B2)) -2))))
	 0))
     ((< (+ (* A2 A1) (* -1 (* B2 B1))) 0)) ((> A2 0)) ((> A1 0)) 
     ((> B1 0)) ((> B2 0))))

We get it easily just by ICP!

So, must instrument inequality chaining/squeezing.

;;
;; Examining factor-sign in waterfall:
;;

Before factor-sign was in waterfall:

 ++ rs(0) proved (0.028f0 s). 
    ++ rs(1) proved (0.03f0 s). 
    -- rs(2) failed. 
    ++ rs(3) proved (0.017f0 s). 
    -- rs(4) failed. 
    -- rs(5) failed. 
    -- rs(6) failed. 
    ++ rs(7) proved (0.072f0 s). 
    -- rs(8) failed. 
    -- rs(9) failed. 
    ++ rs(10) proved (0.036f0 s). 
    -- rs(11) failed. 
    -- rs(12) failed. 
    -- rs(13) failed. 
    ++ rs(14) proved (0.029f0 s). 
    -- rs(15) failed. 
    -- rs(16) failed. 
    -- rs(17) failed. 
    -- rs(18) failed. 
    ++ rs(19) proved (0.184f0 s). 
    -- rs(20) failed. 
    -- rs(21) failed. 
    -- rs(22) failed. 
    ++ rs(23) proved (0.064f0 s). 
    -- rs(24) failed. 
    ++ rs(25) proved (0.042f0 s). 
    ++ rs(26) proved (0.066f0 s). 
    ++ rs(27) proved (0.007f0 s). 
    ++ rs(28) proved (0.009f0 s). 
    -- rs(29) failed. 
    ++ rs(30) proved (0.452f0 s). 
    ++ rs(31) proved (0.063f0 s). 
    -- rs(32) failed. 
    -- rs(33) failed. 
    ++ rs(34) proved (0.03f0 s). 
    -- rs(35) failed. 
    ++ rs(36) proved (0.019f0 s). 
    ++ rs(37) proved (0.003f0 s). 
    -- rs(38) failed. 
    ++ rs(39) proved (0.05f0 s).


After factor-sign was in waterfall:

    ++ rs(0) proved (0.029f0 s). 
    ++ rs(1) proved (0.076f0 s). 
    -- rs(2) failed. 
    ++ rs(3) proved (0.041f0 s). 
    ++ rs(4) proved (0.054f0 s). 
    ++ rs(5) proved (0.077f0 s). 
    -- rs(6) failed. 
    -- rs(7) failed. 
    -- rs(8) failed. 
    -- rs(9) failed. 
    ++ rs(10) proved (0.031f0 s). 
    -- rs(11) failed. 
    -- rs(12) failed. 
    -- rs(13) failed. 
    ++ rs(14) proved (0.0f0 s). 
    -- rs(15) failed. 
    -- rs(16) failed. 
    -- rs(17) failed. 
    -- rs(18) failed. 
    -- rs(19) failed. 
    -- rs(20) failed. 
    -- rs(21) failed. 
    -- rs(22) failed. 
    ++ rs(23) proved (0.097f0 s). 
    -- rs(24) failed. 
    ++ rs(25) proved (0.024f0 s). 
    ++ rs(26) proved (0.082f0 s). 
    ++ rs(27) proved (0.141f0 s). 
    ++ rs(28) proved (0.098f0 s). 
    -- rs(29) failed. 
    ++ rs(30) proved (0.381f0 s). 
    ++ rs(31) proved (0.065f0 s). 
    -- rs(32) failed. 
    -- rs(33) failed. 
    ++ rs(34) proved (0.001f0 s). 
    -- rs(35) failed. 
    ++ rs(36) proved (0.208f0 s). 
    ++ rs(37) proved (0.088f0 s). 
    -- rs(38) failed. 
    ++ rs(39) proved (0.167f0 s).

** Now, after placing it later in the waterfal:

    ++ rs(0) proved (0.013f0 s). 
    ++ rs(1) proved (0.02f0 s). 
    -- rs(2) failed. 
    ++ rs(3) proved (0.021f0 s). 
    ++ rs(4) proved (0.088f0 s). 
    ++ rs(5) proved (0.024f0 s). 
    -- rs(6) failed. 
    ++ rs(7) proved (0.047f0 s). 
    -- rs(8) failed. 
    -- rs(9) failed. 
    ++ rs(10) proved (0.079f0 s). 
    -- rs(11) failed. 
    -- rs(12) failed. 
    -- rs(13) failed. 
    ++ rs(14) proved (0.001f0 s). 
    -- rs(15) failed. 
    -- rs(16) failed. 
    -- rs(17) failed. 
    -- rs(18) failed. 
    ++ rs(19) proved (0.15f0 s). 
    -- rs(20) failed. 
    -- rs(21) failed. 
    -- rs(22) failed. 
    ++ rs(23) proved (0.024f0 s). 
    -- rs(24) failed. 
    ++ rs(25) proved (0.002f0 s). 
    ++ rs(26) proved (0.068f0 s). 
    ++ rs(27) proved (0.006f0 s). 
    ++ rs(28) proved (0.009f0 s). 
    -- rs(29) failed. 
    ++ rs(30) proved (0.415f0 s). 
    ++ rs(31) proved (0.064f0 s). 
    -- rs(32) failed. 
    -- rs(33) failed. 
    ++ rs(34) proved (0.001f0 s). 
    -- rs(35) failed. 
    ++ rs(36) proved (0.055f0 s). 
    ++ rs(37) proved (0.052f0 s). 
    -- rs(38) failed. 
    ++ rs(39) proved (0.058f0 s).

Todo:
;;;
;;; ABANDON-SUBGOALS: Given a case, range of cases, or
;;;  no arguments (interpreted as ``all'') adjust the current
;;;  goal-set of those cases in range so that their 
;;;  spawned subgoals are abandoned.  Note, they are still
;;;  stored in the main *GOAL-SETS* hash-table in case
;;;  we wish to return to them later.
;;; 

;(defun abandon-subgoals (&key from to case)
;  (



Need to deal with catching (- x x)=0 here:

./rahd-v0.6-lx32 -formula "(((> x (/ x (/ y (- x x))))))" -search-model! -print-model




We catch (soundly) a divby0 here:

./rahd-v0.6-lx32 -formula "(((NOT (>= (- (* A1 A2) (* B1 B2)) 0)))
                             ((= (+ (* A1 A1) (* A2 A2))
                                 (+ (* B1 B1) (+ (* B2 B2) 2))))
                             ((= (+ (* A1 B1) (* A2 B2)) 0))
                             ((>= A1 0))
                             ((= (* A1 A2 A3) 0)) ((> A1 (/ 1 A3))))" -verbosity 2







The following causes a waterfall disjunction and we need it to print nicely using cli:

./rahd-v0.6-lx32 -formula "(((NOT (>= (- (* A1 A2) (* B1 B2)) 0)))
                             ((= (+ (* A1 A1) (* A2 A2))
                                 (+ (* B1 B1) (+ (* B2 B2) 2))))
                             ((= (+ (* A1 B1) (* A2 B2)) 0))
                             ((>= A1 0))
                             ((= (* A1 A2) 0)))"




The following makes INTERVAL-CP loop:

     1     ((= (* X X) Y) (> Y 10) (> (+ (* Z Y) -11) 0) (> X Y))    (UNKNOWN
                                                                        SIMP-ZRHS) 



Interesting example re having symbolic values in models:

./rahd-v0.6-lx32 -verbosity 1 -formula "(((> x 10)) ((< x 12)) ((> (+ 12 (* x y 2)) 2000)) ((< y 1000)) ((>= x 10)) ((>= z w)) ((>= k (* z z))))" -search-model! -print-model

[Decision]
 sat
 model: [Y=999,
         X=11,
         K=(* Z Z),
         W=Z].

This is very cool, as it shows us that Z can be any real and then the simple given constraints must be met.
Is this good in general as a feature to have?  Or should we give the user a model w.r.t. an instantiation of Z?

* Note that if we do the counter-model search before we do the refutation cycle, then we find a different
   instantiated model:

./rahd-v0.6-lx32 -verbosity 1 -formula "(((> x 10)) ((< x 12)) ((> (+ 12 (* x y 2)) 2000)) ((< y 1000)) ((>= x 10)) ((>= z w)) ((>= (+ 1 k) (* z z 2))))" -search-model -print-model  

[Decision]
 sat
 model: [Z=0,
         K=-1,
         Y=999,
         X=11,
         W=0].




* Another interesting example where it's better to do counter-model search *before* the refutation cycle, as
   Bounded-GBRNI takes a long time:

./rahd-v0.6-lx32 -verbosity 1 -formula "(((> x 10)) ((< x 12)) ((> (+ 12 (* x y 2)) 2000)) ((< y 1000)) ((>= (* x z) 10)) ((>= z w)) ((>= (+ 1 k) (* z z 2))))" -search-model! -print-model

   ** But if we do the search before, a model is found instantly.




- Idea: Allow Bounded-GBRNI to add PSD >= constraints for discriminants.

(dolist (G685 '(0 1 2))
  (dolist (G697 '(0 1 2))
    (dolist (G699 '(0 1 2))
      (dolist (G683 '(0 1 2))
	(dolist (G710 '(0 1 2))
	  (fmt 0 "~A~%"
	       (+ (* -1/4 (* G685 (* G685 G685)))
		  (+ (* -1 (* (* G697 G697) G685))
		     (+ (* G699 (* G697 G683))
			(+ (* 1/2 (* G699 (* G697 G685)))
			   (+ (* -1/2 (* (* G699 G699) G683))
			      (+ (* -1/4 (* (* G699 G699) G685))
				 (+ (* 3/2 (* G685 G685))
				    (+ (* -2 (* G697 G683))
				       (+ (* 3 (* G697 G685))
					  (+ (* 2 (* G697 G697))
					     (+ (* -3 (* G699 G697))
						(+
						 (* 3/2 (* G699 G699))
						 (+
						  (* 1/2 (* G710 G683))
						  (+
						   (* 1/4
						      (* G710 G685))
						   (+ (* 2 G683)
						      (+ (* -2 G685)
							 (+ (* -2 G697)
							    (+
							     (* -3/2
								G710)
							     -4))))))))))))))))))

	       
;; 

Some notes from Dagstuhl on k(2):

 (g '( ((= (+ (* x0 x0) (* y0 y0)) 4))
       ((= (+ (* x1 x1) (* y1 y1)) 4))
       ((= (+ (* x2 x2) (* y2 y2)) 4))
       ((= (+ (* x3 x3) (* y3 y3)) 4))
       ((= (+ (* x4 x4) (* y4 y4)) 4))
       ((= (+ (* x5 x5) (* y5 y5)) 4))
       ((= (+ (* x6 x6) (* y6 y6)) 4))
       ((>= (+ (* (- x0 x1) (- x0 x1))
	       (* (- y0 y1) (- y0 y1))) 4))
       ((>= (+ (* (- x0 x2) (- x0 x2))
	       (* (- y0 y2) (- y0 y2))) 4))
       ((>= (+ (* (- x0 x3) (- x0 x3))
	       (* (- y0 y3) (- y0 y3))) 4))
       ((>= (+ (* (- x0 x4) (- x0 x4))
	       (* (- y0 y4) (- y0 y4))) 4))
       ((>= (+ (* (- x0 x5) (- x0 x5))
	       (* (- y0 y5) (- y0 y5))) 4))
       ((>= (+ (* (- x0 x6) (- x0 x6))
	       (* (- y0 y6) (- y0 y6))) 4))
       ((>= (+ (* (- x1 x2) (- x1 x2))
	       (* (- y1 y2) (- y1 y2))) 4))
       ((>= (+ (* (- x1 x3) (- x1 x3))
	       (* (- y1 y3) (- y1 y3))) 4))
       ((>= (+ (* (- x1 x4) (- x1 x4))
	       (* (- y1 y4) (- y1 y4))) 4))
       ((>= (+ (* (- x1 x5) (- x1 x5))
	       (* (- y1 y5) (- y1 y5))) 4))
       ((>= (+ (* (- x1 x6) (- x1 x6))
	       (* (- y1 y6) (- y1 y6))) 4))
       ((>= (+ (* (- x2 x3) (- x2 x3))
	       (* (- y2 y3) (- y2 y3))) 4))
       ((>= (+ (* (- x2 x4) (- x2 x4))
	       (* (- y2 y4) (- y2 y4))) 4))
       ((>= (+ (* (- x2 x5) (- x2 x5))
	       (* (- y2 y5) (- y2 y5))) 4))
       ((>= (+ (* (- x2 x6) (- x2 x6))
	       (* (- y2 y6) (- y2 y6))) 4))
       ((>= (+ (* (- x3 x4) (- x3 x4))
	       (* (- y3 y4) (- y3 y4))) 4))
       ((>= (+ (* (- x3 x5) (- x3 x5))
	       (* (- y3 y5) (- y3 y5))) 4))
       ((>= (+ (* (- x3 x6) (- x3 x6))
	       (* (- y3 y6) (- y3 y6))) 4))
       ((>= (+ (* (- x4 x5) (- x4 x5))
	       (* (- y4 y5) (- y4 y5))) 4))
       ((>= (+ (* (- x4 x6) (- x4 x6))
	       (* (- y4 y6) (- y4 y6))) 4))
       ((>= (+ (* (- x5 x6) (- x5 x6))
	       (* (- y5 y6) (- y5 y6))) 4))
       ((>= x0 -2))
       ((<= x0 2))
       ((>= x1 -2))
       ((<= x1 2))
       ((>= x2 -2))
       ((<= x2 2))
       ((>= x3 -2))
       ((<= x3 2))
       ((>= x4 -2))
       ((<= x4 2))
       ((>= x5 -2))
       ((<= x5 2))
       ((>= x6 -2))
       ((<= x6 2))
       ((>= y0 -2))
       ((<= y0 2))
       ((>= y1 -2))
       ((<= y1 2))
       ((>= y2 -2))
       ((<= y2 2))
       ((>= y3 -2))
       ((<= y3 2))
       ((>= y4 -2))
       ((<= y4 2))
       ((>= y5 -2))
       ((<= y5 2))
       ((>= y6 -2))
       ((<= y6 2))

       ))




 (g '( ((= (+ (* a x x) (* b x) c) 0))
       ((< (- (* b b) (* 4 a c)) 0))
       ((>= (- (* b b) (* 4 a c)) 0))))


;; 

Some ideas (7-April-2010)
 - For dealing with arbitrary FOFs, write a `map-over-literals' macro.

;;

Some ideas (25-March-2010):
 - Instrument generalization from <,> to (not =) and then apply GB method a la 
    http://www.risc.uni-linz.ac.at/research/theorema/software/demos/issac/Links/Proof-groebner-bases/index.html.
 - Check out Brown's recent work on simplification re PROP and MONO: http://issac2009.kias.re.kr/Brown.pdf

;; Standalone version crashing (CCL issue) on the following as of 23-Nov-2009:

(g '(((> (+ (* a a) (/ 1 (* x y))) 0))))

./r -formula "(((> (+ (* a a) (/ 1 (* x y))) 0)))" -model-search

;; Current RRS slip-list as of 18-Nov-2009:

? (woo (rrs :skip '(20 21)))

;; 18-Nov-2009 output:

 *** (GO!) invocation on GOAL 0 completed in approximately 0.027 seconds (non-refuted cases remain) *** 

 -------------------------------------------------------------------- 
   RAHD Regression Suite Report 
 -------------------------------------------------------------------- 
    [RRS] ++ RS(0) proved (0.002 s). 
    [RRS] ++ RS(1) proved (0.003 s). 
    [RRS] -- RS(2) FAILED. 
    [RRS] ++ RS(3) proved (0.002 s). 
    [RRS] -- RS(4) FAILED. 
    [RRS] -- RS(5) FAILED. 
    [RRS] -- RS(6) FAILED. 
    [RRS] -- RS(7) FAILED. 
    [RRS] -- RS(8) FAILED. 
    [RRS] -- RS(9) FAILED. 
    [RRS] ++ RS(10) proved (0.023 s). 
    [RRS] -- RS(11) FAILED. 
    [RRS] -- RS(12) FAILED. 
    [RRS] -- RS(13) FAILED. 
    [RRS] -- RS(14) FAILED. 
    [RRS] ++ RS(15) proved (0.0 s). 
    [RRS] -- RS(16) FAILED. 
    [RRS] -- RS(17) FAILED. 
    [RRS] -- RS(18) FAILED. 
    [RRS] -- RS(19) FAILED. 
    [RRS] ## RS(20) skipped. 
    [RRS] ## RS(21) skipped. 
    [RRS] -- RS(22) FAILED. 
    [RRS] -- RS(23) FAILED. 
    [RRS] ++ RS(24) proved (0.0 s). 
    [RRS] -- RS(25) FAILED. 
    [RRS] ++ RS(26) proved (0.001 s). 
    [RRS] -- RS(27) FAILED. 
    [RRS] -- RS(28) FAILED. 
    [RRS] -- RS(29) FAILED. 
    [RRS] -- RS(30) FAILED. 
    [RRS] -- RS(31) FAILED. 
    [RRS] ++ RS(32) proved (0.425 s). 
    [RRS] ++ RS(33) proved (0.0 s). 
    [RRS] -- RS(34) FAILED. 
    [RRS] -- RS(35) FAILED. 
    [RRS] ++ RS(36) proved (0.003 s). 
    [RRS] -- RS(37) FAILED. 
    [RRS] -- RS(38) FAILED. 
    [RRS] ++ RS(39) proved (0.001 s). 
    [RRS] -- RS(40) FAILED. 
    [RRS] -- RS(41) FAILED.


;; 20,21 cause interval constaints to blow up for some reason...





;; Current RRS skip-list as of 17-Sept-2009:

(woo (rrs :skip '(2 9 16 17 19 22 34 35 37)))

[2] can be solved with interval splitting (b1)
       tactic replay: (SIMP-ZRHS 
		       DEMOD-NUM
		       SIMP-GLS
		       SIMP-TVS
		       SIMP-ARITH
		       SIMP-GLS
		       SIMP-TVS
		       CANON-TMS
		       SIMP-REAL-NULL
		       INTVL-SPLIT) ; :var 'B1
 


[9] after three rounds of interval splitting (x,y,z), we have:

 >> PUG: Print goals in GOAL-SET (GOAL ((0 0) 0).1) marked :UNKNOWN (awaiting refutation). 
         Printing all of the remaining one goals.

 -------     -------------------------------------------------------
 CASE-ID     CASE
 -------     -------------------------------------------------------

       1     ((< Y 0) (= (+ (* Y Y) (+ (* Z Z) -1)) 0)
              (> (+ (* 2 (* Z Y)) -2) 0) (< Z 0))    (UNKNOWN) 


 * Idea: Have a CMF that does the following:
    (i) uses RCR-SVARS to recognize that Y^2 = Z^2 + 1,
   (ii) look through other terms to see if an appearance of Y
        could be transformed into an appearance of Y^2 by
        multiplying through by Y.
  (iii) In that case, it would produce:
         (< (+ (* (* 2 (* Z Y)) Y) -2) 0), since Y is already
          known to be negative.  Thus, this CMF is useful *after*
          a case has been fertilized by interval splitting.
   (iv) Then, we can replace the Y^2 by (Z^2 + 1), so we get:
          (< (+ (* 2 (* Z (+ (* Z Z) 1))) -2) 0)
    (v) which canonicalizes to: 
          (< 0 0).
     Q.E.D.


;

* Check for subterms which are squares and intersect with [0,+inf[. (11-Nov-09)



---
*** Work on 16:

? (p)

 >> PUG: Print goals in GOAL-SET (GOAL 0) marked :UNKNOWN (awaiting refutation). 
         Printing all of the remaining seven goals.

 -------     -------------------------------------------------------
 CASE-ID     CASE
 -------     -------------------------------------------------------

       0     ((= (+ (* -1 (* (* B B) (* K K))) (+ (* A A) (* -1 (* B B)))) 0)
              (> (+ (* -1 (* B K)) A) B) (> A 1) (> B 1) (> K 1))    (UNKNOWN
                                                                      SIMP-ZRHS
                                                                      CANON-TMS) 

       1     ((= (+ (* -1 (* (* B B) (* K K))) (+ (* A A) (* -1 (* B B)))) 0)
              (= (+ (* -1 (* B K)) A) B) (> A 1) (> B 1) (> K 1))    (UNKNOWN
                                                                      SIMP-ZRHS
                                                                      CANON-TMS) 

       2     ((= (+ (* -1 (* (* B B) (* K K))) (+ (* -1 (* B B)) 1)) 0)
              (> (+ (* -1 (* B K)) 1) B) (> B 1) (> K 1))    (UNKNOWN
                                                              SIMP-ZRHS
                                                              DEMOD-NUM
                                                              SIMP-GLS
                                                              SIMP-TVS
                                                              SIMP-ARITH
                                                              CANON-TMS) 

       4     ((= (+ (* A A) (+ (* -1 (* K K)) -1)) 0)
              (> (+ A (+ (* -1 K) -1)) 0) (> A 1) (> K 1))    (UNKNOWN
                                                               SIMP-ZRHS
                                                               DEMOD-NUM
                                                               SIMP-GLS
                                                               SIMP-TVS
                                                               SIMP-ARITH
                                                               CANON-TMS
                                                               SIMP-ZRHS) 

       8     ((= (+ (* A A) (* -2 (* B B))) 0) (> (+ A (* -1 B)) B) (> A 1)
              (> B 1))    (UNKNOWN SIMP-ZRHS DEMOD-NUM SIMP-GLS SIMP-TVS
                           SIMP-ARITH CANON-TMS) 

      10     ((= (+ (* -2 (* B B)) 1) 0) (> (+ (* -1 B) 1) B)
              (> B 1))    (UNKNOWN SIMP-ZRHS DEMOD-NUM SIMP-GLS SIMP-TVS
                           SIMP-ARITH CANON-TMS) 

      12     ((= (+ (* A A) -2) 0) (> (+ A -2) 0) (> A 1))    (UNKNOWN
                                                               SIMP-ZRHS
                                                               DEMOD-NUM
                                                               SIMP-GLS
                                                               SIMP-TVS
                                                               SIMP-ARITH
                                                               CANON-TMS
                                                               SIMP-ZRHS) 


 >> PUG: Printing complete. 



         ***     7 cases remain in GOAL-SET (GOAL 0) awaiting refutation      ***

T
? (tr)
(SIMP-ZRHS DEMOD-NUM
           SIMP-GLS
           SIMP-TVS
           SIMP-ARITH
           CANON-TMS
           SIMP-ZRHS
           DEMOD-LIN
           SIMP-GLS
           SIMP-TVS
           RCR-SVARS
           DEMOD-NUM
           SIMP-GLS
           SIMP-TVS
           DEMOD-NUM
           SIMP-GLS
           SIMP-TVS)
