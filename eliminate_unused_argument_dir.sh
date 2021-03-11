#!/bin/bash

TARGET=$1

for FILE in "$TARGET"/*.in
do
  dune exec bin2/eliminate_unused_argument.exe -- "$FILE"
done
