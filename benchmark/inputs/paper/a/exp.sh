#!/bin/sh

LIMIT=900

DIR=termination
OPTION="-gchi -infer-ranking-exparam -termination-split-callsite"
COMMAND="/home/kuwahara/mochi/mochi.opt $OPTION -only-result"
for i in $DIR/*.ml
do
    echo -n $i, | sed 's/\//,/' | sed 's/\.ml//'
    RESULT=$i.result
    TIME=$i.time
    ERROR=$i.error
    TIMEFORMAT='%R'
    time (timeout $LIMIT $COMMAND $i > $RESULT 2> $ERROR) 2> $TIME
    STATUS="$?"
    echo -n $(cat $TIME),
    if [ $STATUS -eq 0 ]; then
        egrep 'minating|Unknown' $RESULT
    else
        echo -
    fi
done

DIR=nonterm
OPTION="-non-termination"
COMMAND="/home/ryosuke/exp/nonterm_bin/mochi $OPTION -only-result"
for i in $DIR/*.ml
do
    echo -n $i, | sed 's/\//,/' | sed 's/\.ml//'
    RESULT=$i.result
    TIME=$i.time
    ERROR=$i.error
    TIMEFORMAT='%R'
    time (timeout $LIMIT $COMMAND $i > $RESULT 2> $ERROR) 2> $TIME
    STATUS="$?"
    echo -n $(cat $TIME),
    if [ $STATUS -eq 0 ]; then
        egrep 'minating|Unknown' $RESULT
    else
        echo -
    fi
done

DIR=fair_termination
OPTION="-fair-termination -bool-init-empty -horsat -rank-widen"
COMMAND="/home/ryosuke/repos/mochi_bins/fair_termination/mochi $OPTION -only-result"
for i in $DIR/*.ml
do
    echo -n $i, | sed 's/\//,/' | sed 's/\.ml//'
    RESULT=$i.result
    TIME=$i.time
    ERROR=$i.error
    TIMEFORMAT='%R'
    time (timeout $LIMIT $COMMAND -fpat '-wp-max 2 -neg-pred' $i > $RESULT 2> $ERROR) 2> $TIME
    STATUS="$?"
    echo -n $(cat $TIME),
    if [ $STATUS -eq 0 ]; then
        egrep 'minating|Unknown' $RESULT
    else
        echo -
    fi
done

DIR=fair_nonterm
OPTION="-fair-non-termination -ins-param-funarg"
COMMAND="/home/watanabe/mochi_bin/mochi $OPTION -only-result"
for i in $DIR/*.ml
do
    echo -n $i, | sed 's/\//,/' | sed 's/\.ml//'
    RESULT=$i.result
    TIME=$i.time
    ERROR=$i.error
    TIMEFORMAT='%R'
    time (timeout $LIMIT $COMMAND -fpat '-wp-max 1 -neg-pred' $i > $RESULT 2> $ERROR) 2> $TIME
    STATUS="$?"
    echo -n $(cat $TIME),
    if [ $STATUS -eq 0 ]; then
        egrep 'Fair Infinite Execution' $RESULT
    else
        echo -
    fi
done

ARC=archive/$(date +"%Y%m%d%H%M")
mkdir -p $ARC
cp -r fair_termination fair_nonterm nonterm termination *.csv $ARC
