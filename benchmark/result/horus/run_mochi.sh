# mode: safety, non-termination, horus
MODE=$1
EXT=.ml
case "$MODE" in
  "safety" )
    DIR=./mochi ;;
  "non-termination" )
    DIR=./mochi-nonterm ;;
  "horus" )
    DIR=./horus
    EXT=.inp ;;
  "horus-cps" )
    DIR=./horus-cps
    EXT=.inp
esac
# for f in ./mochi-nonterm/*.ml; do
for f in ${DIR}/*$EXT; do
  ./run_mochi.js $MODE $f
done
