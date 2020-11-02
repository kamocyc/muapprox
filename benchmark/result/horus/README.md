# Experiments of Horus

We used the attached script file created by Suzuki-san, and fixed by
Iwayama-san.

## For reproductivity

'''
$ ./run_mochi.sh horus > result_1.csv
$ ./run_mochi.sh horus-cps > result_2.csv
'''

We removed the results ended in 'error' in Horus, which indicates
that in the process of verifying, Horus raised an error.
We also removed the instances, whose answer of verification
is false, because Horus cannot prove this kind of system correctly.

