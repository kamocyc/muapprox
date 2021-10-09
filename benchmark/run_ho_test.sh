#!/bin/bash
BENCH_NAME=hoa
COMMON_OPTIONS="--always-add-arguments"

echo '########## full ###########'
python3 bench1.py --timeout 800 --benchmark $BENCH_NAME muapprox_katsura  --pass-args="$COMMON_OPTIONS"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_full.txt 

echo '########## usage ###########'
python3 bench1.py --timeout 800 --benchmark $BENCH_NAME muapprox_katsura --pass-args="$COMMON_OPTIONS --no-partial-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_usage.txt

echo '########## partial ###########'
python3 bench1.py --timeout 800 --benchmark $BENCH_NAME muapprox_katsura --pass-args="$COMMON_OPTIONS --no-usage-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_partial.txt

echo '########## none ###########'
python3 bench1.py --timeout 800 --benchmark $BENCH_NAME muapprox_katsura --pass-args="$COMMON_OPTIONS --no-partial-analysis --no-usage-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_none.txt

echo '########## done ###########'
