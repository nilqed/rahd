;;;
;;; Some default RAHD proof strategies.
;;; Grant Olney Passmore
;;;

(defstrat 'stable-simp
  "repeat [demod-num;
           simp-gls;
           simp-arith]")

(defstrat 'waterfall
  "interval-cp(max-contractions:=20);
   bounded-gbrni;
   split-ineqs;
   interval-cp(max-contractions:=10);
   simp-zrhs;
   run stable-simp;
   demod-lin;
   run stable-simp;
   simp-real-null;
   fert-tsos;
   univ-sturm-ineqs;
   interval-cp;
   satur-lin;
   bounded-gbrni;
   interval-cp;
   triv-ideals;
   canon-tms;
   run stable-simp;
   interval-cp;
   rcr-ineqs;
   run stable-simp;
   fert-tsos;
   run stable-simp;
   interval-cp;
   factor-sign;
   simp-zrhs;
   interval-cp;
   int-dom-zpb;
   quick-sat;
   rcr-ineqs;
   when (dim <= 20) apcad-fd")


(defstrat 'waterfall-with-qepcad-top
  "if (dim < 5)
    [qepcad(open? := 1);
     qepcad]
    redlog-vts;
   interval-cp(max-contractions:=20);
   bounded-gbrni;
   split-ineqs;
   interval-cp(max-contractions:=10);
   simp-zrhs;
   run stable-simp;
   demod-lin;
   run stable-simp;
   simp-real-null;
   fert-tsos;
   univ-sturm-ineqs;
   interval-cp;
   satur-lin;
   bounded-gbrni;
   interval-cp;
   triv-ideals;
   canon-tms;
   run stable-simp;
   interval-cp;
   rcr-ineqs;
   run stable-simp;
   fert-tsos;
   run stable-simp;
   interval-cp;
   factor-sign;
   simp-zrhs;
   interval-cp;
   int-dom-zpb;
   quick-sat;
   rcr-ineqs;
   apcad-fd")

(defstrat 'waterfall-with-qepcad-top
  "if (dim < 5)
    [qepcad(open? := 1);
     qepcad]
    redlog-vts;
   interval-cp(max-contractions:=20);
   bounded-gbrni;
   split-ineqs;
   interval-cp(max-contractions:=10);
   simp-zrhs;
   run stable-simp;
   demod-lin;
   run stable-simp;
   simp-real-null;
   fert-tsos;
   univ-sturm-ineqs;
   interval-cp;
   satur-lin;
   bounded-gbrni;
   interval-cp;
   triv-ideals;
   canon-tms;
   run stable-simp;
   interval-cp;
   rcr-ineqs;
   run stable-simp;
   fert-tsos;
   run stable-simp;
   interval-cp;
   factor-sign;
   simp-zrhs;
   interval-cp;
   int-dom-zpb;
   quick-sat;
   rcr-ineqs;
   apcad-fd")


(defstrat 'waterfall-with-icp-qepcad-redlog
  "interval-cp(max-contractions:=20);
   when (dim <= 5)
    [qepcad(open? := 1);
     qepcad];
   redlog-vts;
   interval-cp(max-contractions:=20);
   bounded-gbrni;
   split-ineqs;
   interval-cp(max-contractions:=10);
   simp-zrhs;
   run stable-simp;
   demod-lin;
   run stable-simp;
   simp-real-null;
   fert-tsos;
   univ-sturm-ineqs;
   interval-cp;
   satur-lin;
   bounded-gbrni;
   interval-cp;
   triv-ideals;
   canon-tms;
   run stable-simp;
   interval-cp;
   rcr-ineqs;
   run stable-simp;
   fert-tsos;
   run stable-simp;
   interval-cp;
   factor-sign;
   simp-zrhs;
   interval-cp;
   int-dom-zpb;
   quick-sat;
   rcr-ineqs;
   apcad-fd;
   redlog-vts")


(defstrat 's-rq-qsat-end
  "interval-cp(max-contractions:=10);
   bounded-gbrni;
   when (dim <= 5) qepcad(open? := 1);
   split-ineqs;
   simp-zrhs;
   run stable-simp;
   if (dim <= 7) qepcad(open? := 1)
     redlog-vts;
   quick-sat")

(defstrat 's-rq-rl-end
  "interval-cp(max-contractions:=10);
   bounded-gbrni;
   when (dim <= 5) qepcad(open? := 1);
   split-ineqs;
   simp-zrhs;
   run stable-simp;
   if (dim <= 7) qepcad(open? := 1)
     redlog-vts;
   interval-cp(max-contractions:=20);
   bounded-gbrni;
   redlog-vts")

(defstrat 's-rq-rl-end-no-bg-end
  "interval-cp(max-contractions:=10);
   bounded-gbrni(gb-bound := nl^2, icp-period:=10);
   when (dim <= 5) qepcad(open? := 1);
   split-ineqs;
   simp-zrhs;
   run stable-simp;
   if (dim <= 7) qepcad(open? := 1)
     redlog-vts;
   interval-cp(max-contractions:=20);
   redlog-vts")

(defstrat 'qepcad-only
  "qepcad")

(defstrat 'icp*-then-qepcad-only
  "interval-cp(max-contractions := 20);
   satur-lin;
   interval-cp(max-contractions := 30);
   qepcad")

(defstrat 'icp-then-qepcad-only
  "interval-cp(max-contractions := 20);
   qepcad")

(defstrat 'qepcad-only-open
  "qepcad(open? := 1)")

(defstrat 'redlog-only
  "redlog-vts")

(defstrat 'qepcad-redlog
  "qepcad;
   redlog-vts")

(defstrat 'qepcad-redlog
  "qepcad(open? := 1);
   redlog-vts")

(defstrat 'icp-gbrni-redlog
  "interval-cp(max-contractions:=10);
   bounded-gbrni;
   redlog-vts")

(defstrat 'icp-only-50
  "interval-cp(max-contractions:=50)")

(defstrat 'calculemus-0
  "split-ineqs(max-splits := 12);
   simp-zrhs;
   run stable-simp;
   demod-lin;
   run stable-simp;
   simp-real-null;
   fert-tsos;
   univ-sturm-ineqs;
   satur-lin;
   triv-ideals;
   run stable-simp;
   rcr-ineqs;
   run stable-simp;
   fert-tsos;
   run stable-simp;
   simp-zrhs;
   int-dom-zpb;
   rcr-ineqs;
   qepcad(open? := 1); 
   qepcad")

(defstrat 'calculemus-1
  "[when (gd = 0) [split-ineqs(max-splits := 12)]];
   interval-cp(max-contractions := 10);
   simp-zrhs;
   run stable-simp;
   demod-lin;
   run stable-simp;
   simp-real-null;
   fert-tsos;
   univ-sturm-ineqs;
   satur-lin;
   interval-cp;
   triv-ideals;
   run stable-simp;
   interval-cp;
   rcr-ineqs;
   run stable-simp;
   fert-tsos;
   run stable-simp;
   interval-cp;
   simp-zrhs;
   interval-cp;
   int-dom-zpb;
   rcr-ineqs;
   when ((dim <= 7) /\\ deg <= 30) 
     [qepcad(open? := 1); qepcad]")


(defstrat 'calculemus-2
  "interval-cp(max-contractions := 10);
   [when ((dim <= 3) /\\ (deg <= 3)) [qepcad]];
   [when ((gd = 0) /\\ dim >= 2) [split-ineqs(max-splits := 12)]];
   interval-cp(max-contractions := 20);
   simp-zrhs;
   run stable-simp;
   demod-lin;
   run stable-simp;
   simp-real-null;
   fert-tsos;
   univ-sturm-ineqs;
   satur-lin;
   interval-cp;
   triv-ideals;
   run stable-simp;
   interval-cp;
   rcr-ineqs;
   run stable-simp;
   fert-tsos;
   run stable-simp;
   interval-cp;
   simp-zrhs;
   interval-cp;
   int-dom-zpb;
   rcr-ineqs;
   when ((dim <= 7) /\\ deg <= 30) 
     [qepcad(open? := 1); qepcad]")


(defstrat 'calculemus-*
  "[when (gd = 0) [split-ineqs(max-splits := 12)]];
   simp-zrhs;
   run stable-simp;
   demod-lin;
   run stable-simp;
   simp-real-null;
   fert-tsos;
   univ-sturm-ineqs;
   satur-lin;
   interval-cp;
   triv-ideals;
   run stable-simp;
   rcr-ineqs;
   run stable-simp;
   fert-tsos;
   run stable-simp;
   simp-zrhs;
   int-dom-zpb;
   rcr-ineqs;
   when ((dim <= 7) /\\ deg <= 30) 
     [qepcad(open? := 1); qepcad]")

(defstrat 'simple-counterexample-finder
 "[quick-sat; run calculemus-0]")
