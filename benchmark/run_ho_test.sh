#!/bin/bash

# extra_termination
# extra_own
# termination_ho
BENCH_NAME=termination_ho

echo '########## noboth ###########'
python3 bench1.py --timeout 900 --benchmark $BENCH_NAME muapprox_katsura_replacer --pass-args="--no-partial-analysis --no-usage-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_noboth.txt

echo '########## noflags ###########'
python3 bench1.py --timeout 900 --benchmark $BENCH_NAME muapprox_katsura_replacer
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_noflags.txt 

echo '########## nopartial ###########'
python3 bench1.py --timeout 900 --benchmark $BENCH_NAME muapprox_katsura_replacer --pass-args="--no-partial-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_nopartial.txt

echo '########## nousage ###########'
python3 bench1.py --timeout 900 --benchmark $BENCH_NAME muapprox_katsura_replacer --pass-args="--no-usage-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_nousage.txt

echo '########## done ###########'
