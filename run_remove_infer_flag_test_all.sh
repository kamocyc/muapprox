#!/bin/bash

DIRS="benchmark/inputs/c_program/ benchmark/inputs/converted/ benchmark/inputs/fairtermination/ benchmark/inputs/first_order/ benchmark/inputs/nontermination/ benchmark/inputs/termination/"

for DIR in $DIRS
do
  find "$DIR" -regex '.*_infer_flag_2\.\(in\|txt\)$' |
  while read -r NAME
  do
    echo "$NAME"
    rm -f "$NAME"
  done
done
