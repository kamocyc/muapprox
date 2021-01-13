#!/bin/bash
rm -f ./*.{hes,in,txt,smt2,tmp}
rm -f pname
rm -f benchmark/output/bench_out_*
rm -f benchmark/output/{z3,hoice}*{in,out}.{txt,smt2}
rm -f benchmark/output/pname
rm -f benchmark/output/{muapprox,sas}_*.txt
rm -f benchmark/output/current.txt
rm -f benchmark/output/_std*.{txt,tmp}
rm -f benchmark/output/*.{tmp,in,smt2}
rm -f benchmark/*.tmp
rm -f benchmark/inputs/mochi/*.{json,smt2,sol,ft.ml}
rm -f benchmark/inputs/mochi/**/*.{json,smt2,sol,ft.ml}
