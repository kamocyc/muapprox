#!/bin/bash
$katsura_solver_path \
  --solver katsura --verbose "${@:2}" \
  "$1" > /tmp/stdout_1.txt 2> /tmp/stderr_1.txt
# --replacer="$(basename "$1" .in)" 
