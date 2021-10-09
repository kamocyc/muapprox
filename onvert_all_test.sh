#!/bin/bash

for FILE in $(find benchmark/inputs/converted/termination -maxdepth 1 -name "*_dual.in")
do
  echo $FILE
  RENAMED=$(echo $FILE | sed -e "s/_dual//")
  echo $RENAMED
  mv $FILE $RENAMED
done


# for FILE in $(find benchmark/inputs/converted/termination -maxdepth 1 -name "*.in")
# do
#   echo $FILE
#   dune exec bin2/dual.exe --  $FILE > /dev/null
#   # cp -f $FILE
# done
