#!/bin/bash

NAMES="array_plus_loop_easy contains_partial list_plus_loop_easy mutual_fixpoints mutual_fixpoints_invalid nested_loop_fact nested_loop_square"

mkdir -p compare && cd compare

for NAME in $NAMES
do
  echo "$NAME"
  cd ..
  dune exec bin2/infer_flag.exe -- --new /opt/home2/git/muapprox/benchmark/research/ho_trans/0_bench/"$NAME"/original.in > out2.txt
  cd -
  # cp /opt/home2/git/muapprox/benchmark/research/ho_trans/0_bench/"$NAME"/03_partial_related_elim.in ./"$NAME"_03.in
  cp /opt/home2/git/muapprox/benchmark/research/ho_trans/0_bench/"$NAME"/original_infer_flag_2.in ./"$NAME"_09_2.in
done

cd ..
