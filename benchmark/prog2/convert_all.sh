#!/bin/bash

cd ..

cd ..
basedir=$(pwd)
cd -

for FILE in $(find prog -name "*.txt")
do
  echo $FILE
  cd "$basedir"
  dune exec bin2/branching_time_program_converter.exe --  benchmark/$FILE > /dev/null
done

