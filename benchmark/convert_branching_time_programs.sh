#!/bin/bash

# run in the project root directory
#  benchmark/prog2/ho benchmark/prog2/fairtermination/ho

DIRPATHS="benchmark/inputs/otest/hflz_ft/"

for DIRPATH in $DIRPATHS
do
  echo DIR: "$DIRPATH"
  for FILE in $(find $DIRPATH -maxdepth 2 -name "*.txt")
  do
    echo $FILE
    dune exec bin2/branching_time_program_converter.exe --  $FILE > /dev/null
  done
done
