
;;;
;;; Some default proof strategies.
;;;

(defstrat 'stable-simp
  "repeat [apply contra-eqs then 
           apply demod-num then 
           apply simp-gls then 
           apply simp-tvs then 
           apply simp-arith]")

(defstrat 'waterfall
  "[apply interval-cp(max-contractions:=10)] then
   [apply simp-zrhs] then
   [run stable-simp] then
   [apply simp-real-null] then
   [apply fert-tsos] then
   [apply univ-sturm-ineqs] then
   [apply interval-cp] then
   [apply satur-lin] then
   [apply bounded-gbrni] then
   [apply interval-cp] then
   [apply triv-ideals] then
   [apply canon-tms] then
   [run stable-simp] then
   [apply interval-cp] then
   [apply rcr-ineqs] then
   [run stable-simp] then
   [apply fert-tsos] then
   [run stable-simp] then
   [apply interval-cp] then
   [apply factor-sign] then
   [apply simp-zrhs] then
   [apply interval-cp] then
   [apply int-dom-zpb] then
   [apply quick-sat] then
   [apply rcr-ineqs]")