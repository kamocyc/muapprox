#!/bin/bash
BENCH_NAME=hoa
COMMON_OPTIONS="--always-add-arguments"

echo '########## noflags ###########'
python3 bench1.py --timeout 800 --benchmark $BENCH_NAME muapprox_katsura  --pass-args="$COMMON_OPTIONS"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_noflags.txt 

echo '########## nopartial ###########'
python3 bench1.py --timeout 800 --benchmark $BENCH_NAME muapprox_katsura --pass-args="$COMMON_OPTIONS --no-partial-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_nopartial.txt

echo '########## nousage ###########'
python3 bench1.py --timeout 800 --benchmark $BENCH_NAME muapprox_katsura --pass-args="$COMMON_OPTIONS --no-usage-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_nousage.txt

echo '########## noboth ###########'
python3 bench1.py --timeout 800 --benchmark $BENCH_NAME muapprox_katsura --pass-args="$COMMON_OPTIONS --no-partial-analysis --no-usage-analysis"
cp output/0bench_out_append.txt_summary.txt 0bench_out_append.txt_summary_bk_noboth.txt

echo '########## done ###########'
