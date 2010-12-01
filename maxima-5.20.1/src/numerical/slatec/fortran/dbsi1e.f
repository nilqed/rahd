*DECK DBSI1E
      DOUBLE PRECISION FUNCTION DBSI1E (X)
C***BEGIN PROLOGUE  DBSI1E
C***PURPOSE  Compute the exponentially scaled modified (hyperbolic)
C            Bessel function of the first kind of order one.
C***LIBRARY   SLATEC (FNLIB)
C***CATEGORY  C10B1
C***TYPE      DOUBLE PRECISION (BESI1E-S, DBSI1E-D)
C***KEYWORDS  EXPONENTIALLY SCALED, FIRST KIND, FNLIB,
C             HYPERBOLIC BESSEL FUNCTION, MODIFIED BESSEL FUNCTION,
C             ORDER ONE, SPECIAL FUNCTIONS
C***AUTHOR  Fullerton, W., (LANL)
C***DESCRIPTION
C
C DBSI1E(X) calculates the double precision exponentially scaled
C modified (hyperbolic) Bessel function of the first kind of order
C one for double precision argument X.  The result is I1(X)
C multiplied by EXP(-ABS(X)).
C
C Series for BI1        on the interval  0.          to  9.00000E+00
C                                        with weighted error   1.44E-32
C                                         log weighted error  31.84
C                               significant figures required  31.45
C                                    decimal places required  32.46
C
C Series for AI1        on the interval  1.25000E-01 to  3.33333E-01
C                                        with weighted error   2.81E-32
C                                         log weighted error  31.55
C                               significant figures required  29.93
C                                    decimal places required  32.38
C
C Series for AI12       on the interval  0.          to  1.25000E-01
C                                        with weighted error   1.83E-32
C                                         log weighted error  31.74
C                               significant figures required  29.97
C                                    decimal places required  32.66
C
C***REFERENCES  (NONE)
C***ROUTINES CALLED  D1MACH, DCSEVL, INITDS, XERMSG
C***REVISION HISTORY  (YYMMDD)
C   770701  DATE WRITTEN
C   890531  Changed all specific intrinsics to generic.  (WRB)
C   890531  REVISION DATE from Version 3.2
C   891214  Prologue converted to Version 4.0 format.  (BAB)
C   900315  CALLs to XERROR changed to CALLs to XERMSG.  (THJ)
C***END PROLOGUE  DBSI1E
      DOUBLE PRECISION X, BI1CS(17), AI1CS(46), AI12CS(69), XMIN,
     1  XSML, Y, D1MACH, DCSEVL
      LOGICAL FIRST
      SAVE BI1CS, AI1CS, AI12CS, NTI1, NTAI1, NTAI12, XMIN, XSML,
     1  FIRST
      DATA BI1CS(  1) / -.1971713261 0998597316 1385032181 49 D-2     /
      DATA BI1CS(  2) / +.4073488766 7546480608 1553936520 14 D+0     /
      DATA BI1CS(  3) / +.3483899429 9959455866 2450377837 87 D-1     /
      DATA BI1CS(  4) / +.1545394556 3001236038 5984010584 89 D-2     /
      DATA BI1CS(  5) / +.4188852109 8377784129 4588320041 20 D-4     /
      DATA BI1CS(  6) / +.7649026764 8362114741 9597039660 69 D-6     /
      DATA BI1CS(  7) / +.1004249392 4741178689 1798080372 38 D-7     /
      DATA BI1CS(  8) / +.9932207791 9238106481 3712980548 63 D-10    /
      DATA BI1CS(  9) / +.7663801791 8447637275 2001716813 49 D-12    /
      DATA BI1CS( 10) / +.4741418923 8167394980 3880919481 60 D-14    /
      DATA BI1CS( 11) / +.2404114404 0745181799 8631720320 00 D-16    /
      DATA BI1CS( 12) / +.1017150500 7093713649 1211007999 99 D-18    /
      DATA BI1CS( 13) / +.3645093565 7866949458 4917333333 33 D-21    /
      DATA BI1CS( 14) / +.1120574950 2562039344 8106666666 66 D-23    /
      DATA BI1CS( 15) / +.2987544193 4468088832 0000000000 00 D-26    /
      DATA BI1CS( 16) / +.6973231093 9194709333 3333333333 33 D-29    /
      DATA BI1CS( 17) / +.1436794822 0620800000 0000000000 00 D-31    /
      DATA AI1CS(  1) / -.2846744181 8814786741 0037246830 7 D-1      /
      DATA AI1CS(  2) / -.1922953231 4432206510 4444877497 9 D-1      /
      DATA AI1CS(  3) / -.6115185857 9437889822 5624991778 5 D-3      /
      DATA AI1CS(  4) / -.2069971253 3502277088 8282377797 9 D-4      /
      DATA AI1CS(  5) / +.8585619145 8107255655 3694467313 8 D-5      /
      DATA AI1CS(  6) / +.1049498246 7115908625 1745399786 0 D-5      /
      DATA AI1CS(  7) / -.2918338918 4479022020 9343232669 7 D-6      /
      DATA AI1CS(  8) / -.1559378146 6317390001 6068096907 7 D-7      /
      DATA AI1CS(  9) / +.1318012367 1449447055 2530287390 9 D-7      /
      DATA AI1CS( 10) / -.1448423418 1830783176 3913446781 5 D-8      /
      DATA AI1CS( 11) / -.2908512243 9931420948 2504099301 0 D-9      /
      DATA AI1CS( 12) / +.1266388917 8753823873 1115969040 3 D-9      /
      DATA AI1CS( 13) / -.1664947772 9192206706 2417839858 0 D-10     /
      DATA AI1CS( 14) / -.1666653644 6094329760 9593715499 9 D-11     /
      DATA AI1CS( 15) / +.1242602414 2907682652 3216847201 7 D-11     /
      DATA AI1CS( 16) / -.2731549379 6724323972 5146142863 3 D-12     /
      DATA AI1CS( 17) / +.2023947881 6458037807 0026268898 1 D-13     /
      DATA AI1CS( 18) / +.7307950018 1168836361 9869812612 3 D-14     /
      DATA AI1CS( 19) / -.3332905634 4046749438 1377861713 3 D-14     /
      DATA AI1CS( 20) / +.7175346558 5129537435 4225466567 0 D-15     /
      DATA AI1CS( 21) / -.6982530324 7962563558 5062922365 6 D-16     /
      DATA AI1CS( 22) / -.1299944201 5627607600 6044608058 7 D-16     /
      DATA AI1CS( 23) / +.8120942864 2427988920 5467834286 0 D-17     /
      DATA AI1CS( 24) / -.2194016207 4107368981 5626664378 3 D-17     /
      DATA AI1CS( 25) / +.3630516170 0296548482 7986093233 4 D-18     /
      DATA AI1CS( 26) / -.1695139772 4391041663 0686679039 9 D-19     /
      DATA AI1CS( 27) / -.1288184829 8979078071 1688253822 2 D-19     /
      DATA AI1CS( 28) / +.5694428604 9670527801 0999107310 9 D-20     /
      DATA AI1CS( 29) / -.1459597009 0904800565 4550990028 7 D-20     /
      DATA AI1CS( 30) / +.2514546010 6757173140 8469133448 5 D-21     /
      DATA AI1CS( 31) / -.1844758883 1391248181 6040002901 3 D-22     /
      DATA AI1CS( 32) / -.6339760596 2279486419 2860979199 9 D-23     /
      DATA AI1CS( 33) / +.3461441102 0310111111 0814662656 0 D-23     /
      DATA AI1CS( 34) / -.1017062335 3713935475 9654102357 3 D-23     /
      DATA AI1CS( 35) / +.2149877147 0904314459 6250077866 6 D-24     /
      DATA AI1CS( 36) / -.3045252425 2386764017 4620617386 6 D-25     /
      DATA AI1CS( 37) / +.5238082144 7212859821 7763498666 6 D-27     /
      DATA AI1CS( 38) / +.1443583107 0893824464 1678950399 9 D-26     /
      DATA AI1CS( 39) / -.6121302074 8900427332 0067071999 9 D-27     /
      DATA AI1CS( 40) / +.1700011117 4678184183 4918980266 6 D-27     /
      DATA AI1CS( 41) / -.3596589107 9842441585 3521578666 6 D-28     /
      DATA AI1CS( 42) / +.5448178578 9484185766 5051306666 6 D-29     /
      DATA AI1CS( 43) / -.2731831789 6890849891 6256426666 6 D-30     /
      DATA AI1CS( 44) / -.1858905021 7086007157 7190399999 9 D-30     /
      DATA AI1CS( 45) / +.9212682974 5139334411 2776533333 3 D-31     /
      DATA AI1CS( 46) / -.2813835155 6535611063 7083306666 6 D-31     /
      DATA AI12CS(  1) / +.2857623501 8280120474 4984594846 9 D-1      /
      DATA AI12CS(  2) / -.9761097491 3614684077 6516445730 2 D-2      /
      DATA AI12CS(  3) / -.1105889387 6262371629 1256921277 5 D-3      /
      DATA AI12CS(  4) / -.3882564808 8776903934 5654477627 4 D-5      /
      DATA AI12CS(  5) / -.2512236237 8702089252 9452002212 1 D-6      /
      DATA AI12CS(  6) / -.2631468846 8895195068 3705236523 2 D-7      /
      DATA AI12CS(  7) / -.3835380385 9642370220 4500678796 8 D-8      /
      DATA AI12CS(  8) / -.5589743462 1965838068 6811252222 9 D-9      /
      DATA AI12CS(  9) / -.1897495812 3505412344 9892503323 8 D-10     /
      DATA AI12CS( 10) / +.3252603583 0154882385 5508067994 9 D-10     /
      DATA AI12CS( 11) / +.1412580743 6613781331 6336633284 6 D-10     /
      DATA AI12CS( 12) / +.2035628544 1470895072 2452613684 0 D-11     /
      DATA AI12CS( 13) / -.7198551776 2459085120 9258989044 6 D-12     /
      DATA AI12CS( 14) / -.4083551111 0921973182 2849963969 1 D-12     /
      DATA AI12CS( 15) / -.2101541842 7726643130 1984572746 2 D-13     /
      DATA AI12CS( 16) / +.4272440016 7119513542 9778833699 7 D-13     /
      DATA AI12CS( 17) / +.1042027698 4128802764 1741449994 8 D-13     /
      DATA AI12CS( 18) / -.3814403072 4370078047 6707253539 6 D-14     /
      DATA AI12CS( 19) / -.1880354775 5107824485 1273453396 3 D-14     /
      DATA AI12CS( 20) / +.3308202310 9209282827 3190335240 5 D-15     /
      DATA AI12CS( 21) / +.2962628997 6459501390 6854654205 2 D-15     /
      DATA AI12CS( 22) / -.3209525921 9934239587 7837353288 7 D-16     /
      DATA AI12CS( 23) / -.4650305368 4893583255 7128281897 9 D-16     /
      DATA AI12CS( 24) / +.4414348323 0717079499 4611375964 1 D-17     /
      DATA AI12CS( 25) / +.7517296310 8421048054 2545808029 5 D-17     /
      DATA AI12CS( 26) / -.9314178867 3268833756 8484784515 7 D-18     /
      DATA AI12CS( 27) / -.1242193275 1948909561 1678448869 7 D-17     /
      DATA AI12CS( 28) / +.2414276719 4548484690 0515390217 6 D-18     /
      DATA AI12CS( 29) / +.2026944384 0532851789 7192286069 2 D-18     /
      DATA AI12CS( 30) / -.6394267188 2690977870 4391988681 1 D-19     /
      DATA AI12CS( 31) / -.3049812452 3730958960 8488450357 1 D-19     /
      DATA AI12CS( 32) / +.1612841851 6514802251 3462230769 1 D-19     /
      DATA AI12CS( 33) / +.3560913964 3099250545 1027090462 0 D-20     /
      DATA AI12CS( 34) / -.3752017947 9364390796 6682800324 6 D-20     /
      DATA AI12CS( 35) / -.5787037427 0747993459 5198231074 1 D-22     /
      DATA AI12CS( 36) / +.7759997511 6481619619 8236963209 2 D-21     /
      DATA AI12CS( 37) / -.1452790897 2022333940 6445987408 5 D-21     /
      DATA AI12CS( 38) / -.1318225286 7390367021 2192275337 4 D-21     /
      DATA AI12CS( 39) / +.6116654862 9030707018 7999133171 7 D-22     /
      DATA AI12CS( 40) / +.1376279762 4271264277 3024338363 4 D-22     /
      DATA AI12CS( 41) / -.1690837689 9593478849 1983938230 6 D-22     /
      DATA AI12CS( 42) / +.1430596088 5954331539 8720108538 5 D-23     /
      DATA AI12CS( 43) / +.3409557828 0905940204 0536772990 2 D-23     /
      DATA AI12CS( 44) / -.1309457666 2707602278 4573872642 4 D-23     /
      DATA AI12CS( 45) / -.3940706411 2402574360 9352141755 7 D-24     /
      DATA AI12CS( 46) / +.4277137426 9808765808 0616679735 2 D-24     /
      DATA AI12CS( 47) / -.4424634830 9826068819 0028312302 9 D-25     /
      DATA AI12CS( 48) / -.8734113196 2307149721 1530978874 7 D-25     /
      DATA AI12CS( 49) / +.4045401335 6835333921 4340414242 8 D-25     /
      DATA AI12CS( 50) / +.7067100658 0946894656 5160771780 6 D-26     /
      DATA AI12CS( 51) / -.1249463344 5651052230 0286451860 5 D-25     /
      DATA AI12CS( 52) / +.2867392244 4034370329 7948339142 6 D-26     /
      DATA AI12CS( 53) / +.2044292892 5042926702 8177957421 0 D-26     /
      DATA AI12CS( 54) / -.1518636633 8204625683 7134680291 1 D-26     /
      DATA AI12CS( 55) / +.8110181098 1875758861 3227910703 7 D-28     /
      DATA AI12CS( 56) / +.3580379354 7735860911 2717370327 0 D-27     /
      DATA AI12CS( 57) / -.1692929018 9279025095 9305717544 8 D-27     /
      DATA AI12CS( 58) / -.2222902499 7024276390 6775852777 4 D-28     /
      DATA AI12CS( 59) / +.5424535127 1459696550 4860040112 8 D-28     /
      DATA AI12CS( 60) / -.1787068401 5780186887 6491299330 4 D-28     /
      DATA AI12CS( 61) / -.6565479068 7228149388 2392943788 0 D-29     /
      DATA AI12CS( 62) / +.7807013165 0611452809 2206770683 9 D-29     /
      DATA AI12CS( 63) / -.1816595260 6689797173 7933315222 1 D-29     /
      DATA AI12CS( 64) / -.1287704952 6600848203 7687559895 9 D-29     /
      DATA AI12CS( 65) / +.1114548172 9881645474 1370927369 4 D-29     /
      DATA AI12CS( 66) / -.1808343145 0393369391 5936887668 7 D-30     /
      DATA AI12CS( 67) / -.2231677718 2037719522 3244822893 9 D-30     /
      DATA AI12CS( 68) / +.1619029596 0803415106 1790980361 4 D-30     /
      DATA AI12CS( 69) / -.1834079908 8049414139 0130843921 0 D-31     /
      DATA FIRST /.TRUE./
C***FIRST EXECUTABLE STATEMENT  DBSI1E
      IF (FIRST) THEN
         ETA = 0.1*REAL(D1MACH(3))
         NTI1 = INITDS (BI1CS, 17, ETA)
         NTAI1 = INITDS (AI1CS, 46, ETA)
         NTAI12 = INITDS (AI12CS, 69, ETA)
C
         XMIN = 2.0D0*D1MACH(1)
         XSML = SQRT(4.5D0*D1MACH(3))
      ENDIF
      FIRST = .FALSE.
C
      Y = ABS(X)
      IF (Y.GT.3.0D0) GO TO 20
C
      DBSI1E = 0.0D0
      IF (Y.EQ.0.D0)  RETURN
C
      IF (Y .LE. XMIN) CALL XERMSG ('SLATEC', 'DBSI1E',
     +   'ABS(X) SO SMALL I1 UNDERFLOWS', 1, 1)
      IF (Y.GT.XMIN) DBSI1E = 0.5D0*X
      IF (Y.GT.XSML) DBSI1E = X*(0.875D0 + DCSEVL (Y*Y/4.5D0-1.D0,
     1  BI1CS, NTI1) )
      DBSI1E = EXP(-Y) * DBSI1E
      RETURN
C
 20   IF (Y.LE.8.D0) DBSI1E = (0.375D0 + DCSEVL ((48.D0/Y-11.D0)/5.D0,
     1  AI1CS, NTAI1))/SQRT(Y)
      IF (Y.GT.8.D0) DBSI1E = (0.375D0 + DCSEVL (16.D0/Y-1.D0, AI12CS,
     1  NTAI12))/SQRT(Y)
      DBSI1E = SIGN (DBSI1E, X)
C
      RETURN
      END
