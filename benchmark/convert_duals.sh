#!/bin/bash

DIRPATH=benchmark/inputs/otest/hflz_ft/

rm $DIRPATH/*_dual.in

for ORGFILE in $(find $DIRPATH -maxdepth 2 -name "*.in")
do
  echo $ORGFILE
  dune exec bin2/dual.exe --  $ORGFILE > /dev/null
  
  FILE="${ORGFILE%.*}"_dual.in
  RENAMED=$(echo $FILE | sed -e "s/_dual//")
  echo $RENAMED
  mv $FILE $RENAMED
done
