#!/bin/bash

: > summary.log

for file in benchmark/research/ho_trans/**/*.log
do
  echo "$file"
  
  result=$(grep -Pazo 'Verification Result:\n  \w+' "$file" | tr -d '\0' | tail -n 1 | awk '{print $1}')
  time=$(grep -Pazo 'Profiling:\n  total: \d+\.\d+ sec'  "$file" | tr -d '\0' | tail -n 1 | awk '{print $2}')
  
  if [ -z "$result" ]
  then
    echo "$file" timeout timeout >> summary.log
  else
    echo "$file" "$result" "$time" >> summary.log
  fi
done
