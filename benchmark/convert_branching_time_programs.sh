#!/bin/bash

# run in the project root directory
#  benchmark/prog2/ho benchmark/prog2/fairtermination/ho

if [ $# != 2 ]; then
  echo "Error: specify target directory and maxdepth"
fi

DIRPATH=$1
MAXDEPTH=$2

# for DIRPATH in $DIRPATHS
# do
#   echo DIR: "$DIRPATH"
  for FILE in $(find $DIRPATH -maxdepth $MAXDEPTH -name "*.txt")
  do
    echo $FILE
    dune exec bin2/branching_time_program_converter.exe --  $FILE > /dev/null
  done
# done
