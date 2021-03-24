#!/bin/bash
/opt/home2/git/muapprox/_build/default/bin/muapprox_main.exe \
  --verbose "${@:2}" \
  --no-inlining-backend --no-simplify "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt
# --first-order-solver 