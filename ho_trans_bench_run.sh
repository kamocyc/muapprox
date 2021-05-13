#!/bin/bash

base_path=benchmark/research/ho_trans/0_bench

function run_hoice() {
  timeout 5m ./y --solver=hoice --dont "$base_path"/"$1" > "$base_path"/"$1"_hoice.log
}
function run_z3() {
  timeout 5m ./y --solver=z3 --dont "$base_path"/"$1" > "$base_path"/"$1"_z3.log
}

while read -r line
do
  echo "$line"
  
  # run in parallel
  run_hoice "$line" &
  PID1=$!
  
  run_z3 "$line" &
  PID2=$!
  
  wait $PID1
  wait $PID2
  
  ./killp.sh
  
  # timeout 5m ./y --solver=hoice --dont "$base_path"/"$line" > "$base_path"/"$line"_hoice.log
  # ./killp.sh
  # timeout 5m ./y --solver=z3 --dont "$base_path"/"$line" > "$base_path"/"$line"_z3.log
  # ./killp.sh
done < benchmark/read_list.txt
