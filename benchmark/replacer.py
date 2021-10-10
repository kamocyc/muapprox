import sys
import uuid
import tempfile
import os
import argparse
import glob
import re

os.chdir(os.path.dirname(__file__))

def replace(buf, sources, targets):
    errors = []
    for i, source in enumerate(sources):
        target = targets[i]
        occ_count = buf.count(source)
        if occ_count == 0:
            errors.append('target string not found (' + source + ')')
        elif occ_count >= 2:
            errors.append('multiple target strings found (' + source + ')')
        else:
            buf = buf.replace(source, target)
    
    if errors == []:
        return 0, buf
    else:
        return 1, '\n'.join(errors)

parser = argparse.ArgumentParser(description='replacer.')
parser.add_argument('target_name', type=str)
parser.add_argument('input_filename', type=str)
parser.add_argument('--check-target-name-only', action='store_true')
parser.add_argument('--mode', type=str, default='')

args = parser.parse_args()

target_name = args.target_name
input_filename = args.input_filename
check_target_name_only = args.check_target_name_only
mode = args.mode

replacement_names = [ os.path.splitext(os.path.basename(s))[0] for s in glob.glob("./replacer/*.txt")]

if not target_name in replacement_names:
    print('Error: illegal target name')
    sys.exit(3)

if check_target_name_only:
    print('ok')
    sys.exit(0)

try:
    with open(input_filename, 'r') as f:
        buf = "".join(f.readlines())
except FileNotFoundError:
    print("Error: file \"" + input_filename + "\" not found")
    sys.exit(1)

def replace_escaped(s):
    return s.replace("^n","\n")
    
with open('replacer/' + target_name + '.txt', 'r') as f:
    # buf = '\n'.join(f.readlines())
    # if mode != '':
    #     buf = re.split("^\\w*#!.*" + mode + ".*$", buf)
    
    lines = f.readlines()
    lines = [ line for line in [l.strip() for l in lines] if line != '' and (line[0] != '#' or line[1] == '!') ]
    
    if mode != '':
        is_getting = False
        found_shbang = False
        results = []
        for index, line in enumerate(lines):
            if line[0:2] == '#!':
                found_shbang = True
                if is_getting:
                    break
                elif re.match('^\\w*#!.*' + mode + '.*$', line):
                    is_getting = True
            elif is_getting:
                results.append(line)
    
        if found_shbang:
            if results == []:
                print("Error: mode \"" + mode + "\" not found")
            
            lines = results
    
    if len(lines) % 2 != 0:
        print('illegal line number')
        sys.exit(1)
    
    sources = [replace_escaped(s) for i, s in enumerate(lines) if i % 2 == 0]
    targets = [replace_escaped(s) for i, s in enumerate(lines) if i % 2 == 1]

status, buf = replace(buf, sources, targets)

if status == 0:
    tempfilename = os.path.join(tempfile.gettempdir(), str(uuid.uuid4()) + ".tmp")

    with open(tempfilename, 'w') as f:
        f.write(buf)
        
    print(tempfilename)
    sys.exit(0)
else:
    print('Error:\n' + buf)
    sys.exit(1)
