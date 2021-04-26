#!/bin/bash

# result: https://docs.google.com/spreadsheets/d/1c0vSsDlZpV81mH1peugVLUTT7xTi8VmvVkz0f_-5Wqk/edit?usp=sharing

omit_minus=1
gen=gen.js

min=10
max=200
step=10
solver=z3

# min=10
# max=200
# step=10
# solver=hoice

dir="$(dirname "${BASH_SOURCE[0]}")"

: > "$dir"/result.txt

i=$min
while [ $i -le  $max ]
do
  echo "number of variables:" $i
  node "$dir"/"$gen" $i $omit_minus > "$dir"/tmp.in
  /opt/home2/git/hflmc2_mora/_build/default/bin/main.exe --solver=$solver "$dir"/tmp.in > "$dir"/tmp.txt
  echo $i "$(grep --color=never "CHC Solver" benchmark/research/many_vars/tmp.txt | awk '{print $3}')" >>  "$dir"/result.txt
  ((i=i+step))
done

