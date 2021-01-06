import os
import ast

os.chdir('output')
OUTPUT_FILE_NAME = 'bench_out_summary.txt'

with open(OUTPUT_FILE_NAME, 'r') as f:
    text = f.read()

data = ast.literal_eval(text)

lines = []
for i, row in enumerate(data):
    lines.append(row['result'] + '\t' + str(row['time']) + '\n')

with open(OUTPUT_FILE_NAME + '_table.txt', 'w') as f:
    f.writelines(lines)
