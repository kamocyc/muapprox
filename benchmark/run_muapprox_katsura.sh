#!/bin/bash
/opt/home2/git/muapprox/_build/default/bin/main.exe --solver katsura --verbose --no-inlining --no-simplify --ignore-unknown --no-inlining-backend "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt
