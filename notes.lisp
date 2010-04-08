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
