
;;;
;;; Some default proof strategies.
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
   fdep-cad")

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
   bounded-gbrni;
   when (dim <= 5) qepcad(open? := 1);
   split-ineqs;
   simp-zrhs;
   run stable-simp;
   if (dim <= 7) qepcad(open? := 1)
     redlog-vts;
   interval-cp(max-contractions:=20);
   redlog-vts")