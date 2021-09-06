#!/bin/bash

# とりあえず、全部処理してみる
# benchmark/inputs/c_program/ 
DIRS="benchmark/inputs/c_program/ benchmark/inputs/converted/ benchmark/inputs/fairtermination/ benchmark/inputs/first_order/ benchmark/inputs/nontermination/ benchmark/inputs/termination/"

for DIR in $DIRS
do
  find "$DIR" -regex '.*\.\(txt\|in\)$' |
  while read -r NAME
  do
    if ! [[ $VAR =~ .*_infer_flag_2\.(txt|in)$ ]]; then
      echo "$NAME"
      dune exec bin2/infer_flag.exe -- --new "$NAME" > out2.txt
    fi
  done
done
