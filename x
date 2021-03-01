#!/bin/bash

dune exec ./bin/muapprox_main.exe -- --no-inlining --no-simplify "$@"
