#!/bin/bash

# run in the project root directory
#  benchmark/prog2/ho benchmark/prog2/fairtermination/ho

DIRPATHS="benchmark/prog2/mucalculus_as_ft/ver2 benchmark/prog2/fairtermination_2"

for DIRPATH in $DIRPATHS
do
  echo DIR: "$DIRPATH"
  for FILE in $(find $DIRPATH -maxdepth 1 -name "*.txt")
  do
    echo $FILE
    dune exec bin2/branching_time_program_converter.exe --  $FILE > /dev/null
  done
done
