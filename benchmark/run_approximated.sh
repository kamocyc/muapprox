#!/bin/bash

# ファイルが異なる！
DIRPATH=benchmark/inputs/otest

mkdir temp_approximated

for FILE in $(find $DIRPATH -maxdepth 2 -name "*.in")
do
  echo $FILE  
  FLAGS="--no-au --coe=1,1 --coe-arg=1,1 --replacer=$(basename "$FILE" .in)"
  
  timeout 5 ./x $FLAGS $FILE > /dev/null 2>&1
  SOURCE=$(basename "$FILE")
  cp "$SOURCE"__prover__1.in temp_approximated/"$SOURCE"__noflags.in
  ./killp.sh 2> /dev/null
  
  timeout 5 ./x --no-par $FLAGS $FILE > /dev/null 2>&1
  cp "$SOURCE"__prover__1.in temp_approximated/"$SOURCE"__nopartial.in
  ./killp.sh 2> /dev/null
  
  timeout 5 ./x --no-usage $FLAGS $FILE > /dev/null 2>&1
  cp "$SOURCE"__prover__1.in temp_approximated/"$SOURCE"__nousage.in
  ./killp.sh 2> /dev/null
  
  timeout 5 ./x --no-par --no-usage $FLAGS $FILE > /dev/null 2>&1
  cp "$SOURCE"__prover__1.in temp_approximated/"$SOURCE"__noboth.in
  ./killp.sh 2> /dev/null
done
