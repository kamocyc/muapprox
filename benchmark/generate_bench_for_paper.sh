#!/bin/bash

set -eux

ROOT_PATH=benchmark/inputs/paper

rm -f $ROOT_PATH/*/*.in

bash benchmark/ml2hfls.sh $ROOT_PATH/nonterm 1
bash benchmark/ml2hfls.sh $ROOT_PATH/termination 1
bash benchmark/convert_duals.sh $ROOT_PATH/termination 1
bash benchmark/ml2hfls.sh $ROOT_PATH/termination_ho 1
bash benchmark/convert_duals.sh $ROOT_PATH/termination_ho 1

bash benchmark/convert_branching_time_programs.sh $ROOT_PATH/fair_nonterm 1
bash benchmark/convert_branching_time_programs.sh $ROOT_PATH/fair_termination 1
bash benchmark/convert_duals.sh $ROOT_PATH/fair_termination 1
bash benchmark/convert_branching_time_programs.sh $ROOT_PATH/fair_termination_ho 1
bash benchmark/convert_duals.sh $ROOT_PATH/fair_termination_ho 1
