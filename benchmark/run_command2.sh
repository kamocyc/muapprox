#!/bin/bash
# /opt/home2/git/muapprox/_build/default/bin/main.exe --hes --first-order-solver --verbose "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt
/opt/home2/git/muapprox/_build/default/bin/main.exe --hes --solver katsura --verbose --no-inlining --no-inlining-backend --no-simplify "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt
# /opt/home2/git/muapprox/_build/default/bin/main.exe --hes --solver iwayama --verbose "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt