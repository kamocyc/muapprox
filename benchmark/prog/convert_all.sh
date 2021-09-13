#!/bin/bash

cd ..

cd ..
basedir=$(pwd)
cd -

for FILE in $(find prog -name "*.txt")
do
  echo $FILE
  cd "$basedir"
  # dune exec bin2/ltl_converter.exe -- benchmark/$FILE > /dev/null
  dune exec bin2/ltl_converter.exe -- --use-b benchmark/$FILE > /dev/null
done
