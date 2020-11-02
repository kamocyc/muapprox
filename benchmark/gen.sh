#!/bin/bash

cd inputs

LISTS=`ls | grep -E "[^n]$"`
echo $LISTS

mkdir -p ../lists
rm -f ../lists/all

for l in $LISTS
do

    echo $l
    find $l -depth 1 | grep -E ".*in$" > ../lists/$l
    find $l -depth 1 | grep -E ".*in$" >> ../lists/all
done

l="test_safe_2019"
find $l -depth 2 | grep -E ".*in$" > ../lists/$l
find $l -depth 2 | grep -E ".*in$" >> ../lists/all

cd ../
# adhoc
mv lists/Burn_POPL18 lists/burn
mv lists/Burn_POPL18_2 lists/burn2
mv lists/higher_nonterminating lists/nonterminating
cat lists/mochi lists/mochi2 > lists/mochis


############ HOCHC ##################

cd hochcs
LISTS=`ls  | grep -E "[^n]$"`
mkdir -p ../lists
rm -f ../lists/horus_all

for l in $LISTS
do
    find $l -depth 1 | grep -E ".*inp$" > ../lists/$l
    find $l -depth 1 | grep -E ".*inp$" >> ../lists/horusall
done
cd ../


############ ML ##################
cd ml
l="test_safe_2019"
find $l -depth 2 | grep -E ".*ml$" > ../lists/ml
cd ../

cd ml
l="higher_nonterminating"
find $l -depth 1 | grep -E ".*ml$" > ../lists/ml-nonterminating
cd ../
