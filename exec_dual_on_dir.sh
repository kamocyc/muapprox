#!/bin/bash
set -euxo pipefail

if [ "$#" -ne 2 ]; then
  >&2 echo "ERROR: illegal number of parameters. please specify source and target directory"
  exit 1
fi

SOURCE=$1
TARGET=$2

for FILE in "$SOURCE"/*.in
do
  TEMP_PATH="$SOURCE"/"$(basename -s .in "$FILE")"_dual.in
  if [ -f "$TEMP_PATH" ]; then
    >&2 echo ERROR: a file \""$TEMP_PATH"\" already exists
    exit 1
  fi
  
  TARGET_PATH="$TARGET"/"$(basename "$FILE")"
  if [ -f "$TARGET_PATH" ]; then
    >&2 echo ERROR: In the target, a file \""$TARGET_PATH"\" already exists
    exit 1
  fi
  
  dune exec bin2/dual.exe -- "$FILE"
  
  mv -n "$TEMP_PATH" "$TARGET_PATH"
done
