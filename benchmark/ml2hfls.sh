#!/bin/bash

if [ $# != 2 ]; then
  echo "Error: specify target directory and maxdepth"
  exit 1
fi

DIRPATH=$1
MAXDEPTH=$2

for ORGFILE in $(find $DIRPATH -maxdepth $MAXDEPTH -name "*.ml")
do
  echo $ORGFILE
  bash benchmark/ml2hfl.sh $ORGFILE > /dev/null
  retVal=$?
  if [ $retVal != 0 ]; then
    echo "Error: \$?="$retVal
    exit $retVal
  fi
done
