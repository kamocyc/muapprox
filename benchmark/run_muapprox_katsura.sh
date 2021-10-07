#!/bin/bash
/opt/home2/git/muapprox/_build/default/bin/muapprox_main.exe \
  --no-au --solver katsura --no-simplify --verbose "${@:2}" \
  "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt
