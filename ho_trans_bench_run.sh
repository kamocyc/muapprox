#!/bin/bash

while read -r line
do
  echo "$line"
  timeout 5m ./y --solver=hoice --dont benchmark/research/ho_trans/"$line" > benchmark/research/ho_trans/"$line"_hoice.log
  ./killp.sh
  timeout 5m ./y --solver=z3 --dont benchmark/research/ho_trans/"$line" > benchmark/research/ho_trans/"$line"_z3.log
  ./killp.sh
done < benchmark/read_list.txt
