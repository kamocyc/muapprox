#!/bin/bash
/opt/home2/git/muapprox/_build/default/bin/main.exe \
  --solver katsura --verbose --no-inlining --no-simplify \
  --solver-backend=z3 \
  --ignore-unknown --kill-processes "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt
