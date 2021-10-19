#!/bin/bash

if [ $# != 1 ]; then
  echo "Error: target file path"
  exit 1
fi

FILE="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"

# specify this path
cd ../ml2hfl*

./x "$FILE"
retVal=$?

cd -

exit $retVal
