#!/bin/bash

# extra_termination
# extra_own
# termination_ho
BENCH_NAME=all_1

echo '########## noflags ###########'
python3 bench1.py --timeout 900 --benchmark $BENCH_NAME muapprox_katsura_replacer
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_noflags.txt 

echo '########## nopartial ###########'
python3 bench1.py --timeout 900 --benchmark $BENCH_NAME muapprox_katsura_replacer --pass-args="--no-partial-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_nopartial.txt

echo '########## nousage ###########'
python3 bench1.py --timeout 900 --benchmark $BENCH_NAME muapprox_katsura_replacer --pass-args="--no-usage-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_nousage.txt

echo '########## noboth ###########'
python3 bench1.py --timeout 900 --benchmark $BENCH_NAME muapprox_katsura_replacer --pass-args="--no-partial-analysis --no-usage-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_noboth.txt

echo '########## done ###########'
