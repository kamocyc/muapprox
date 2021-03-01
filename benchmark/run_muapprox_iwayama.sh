#!/bin/bash
/opt/home2/git/muapprox/_build/default/bin/muapprox_main.exe \
  --solver iwayama --verbose --no-inlining \
  --no-simplify "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt

# --solver-backend options is for preventing duplicate of work (iwayama solver does not have --solver option)

# --hes 
# --no-inlining-backend