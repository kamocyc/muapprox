#!/bin/bash

# run in the project root directory

DIRPATH=benchmark/prog2/fairtermination

for FILE in $(find $DIRPATH -name "*.txt")
do
  echo $FILE
  dune exec bin2/branching_time_program_converter.exe --  $FILE > /dev/null
done

