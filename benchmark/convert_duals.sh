#!/bin/bash

if [ $# != 2 ]; then
  echo "Error: specify target directory and maxdepth"
  exit 1
fi

DIRPATH=$1
MAXDEPTH=$2

rm "$DIRPATH"/*_dual.in

for ORGFILE in $(find $DIRPATH -maxdepth $MAXDEPTH -name "*.in")
do
  echo $ORGFILE
  dune exec bin2/dual.exe --  $ORGFILE > /dev/null
  
  FILE="${ORGFILE%.*}"_dual.in
  RENAMED=$(echo $FILE | sed -e "s/_dual//")
  mv $FILE $RENAMED
done
