#!/bin/bash
# run katsura-solver

$katsura_solver_path --solve-dual=auto-conservative --z3-path=/usr/bin/z3 "$@"
