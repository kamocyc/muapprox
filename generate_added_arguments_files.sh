#!/bin/bash

dir=benchmark/research/ho_trans/0_bench/nested_loop_fact
file="$dir"/original.in
coe=1,1
coe_a=1,0

timeout 5s ./x --coe=$coe --coe-a=$coe_a --add-arg "$file"
. ./killp.sh
cp original.in__prover__1.in "$dir"/01_none.in

timeout 5s ./x --coe=$coe --coe-a=$coe_a --add-arg --partial "$file"
. ./killp.sh
cp original.in__prover__1.in "$dir"/02_partial.in

timeout 5s ./x --coe=$coe --coe-a=$coe_a --add-arg --partial --use-r --elim "$file"
. ./killp.sh
cp original.in__prover__1.in "$dir"/03_partial_related_elim.in

timeout 5s ./x --coe=$coe --coe-a=$coe_a --add-arg --partial --use-r "$file"
. ./killp.sh
cp original.in__prover__1.in "$dir"/04_partial_related.in

timeout 5s ./x --coe=$coe --coe-a=$coe_a --add-arg --partial --elim "$file"
. ./killp.sh
cp original.in__prover__1.in "$dir"/05_partial_elim.in

timeout 5s ./x --coe=$coe --coe-a=$coe_a --add-arg --use-r --elim "$file"
. ./killp.sh
cp original.in__prover__1.in "$dir"/06_related_elim.in

