#!/bin/bash

dune exec ./bin/main.exe -- --no-inlining --no-simplify --ignore-unknown "$@"
