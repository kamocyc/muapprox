#!/bin/bash
/opt/home2/git/muapprox/_build/default/bin/muapprox_main.exe \
  --solver iwayama --verbose --no-inlining \
  --no-simplify --ignore-unknown --kill-processes "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt

# --hes 
# --no-inlining-backend