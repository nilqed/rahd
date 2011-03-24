;;;
;;; Some default RAHD proof strategies.
;;; Grant Olney Passmore
;;;

(defstrat 'stable-simp
  "repeat [contra-eqs;
           demod-num;
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