from pprint import pprint
import json
import os
import subprocess
# import signal   
import time
import re
# import sys
import argparse

if os.path.basename(os.getcwd()) == 'benchmark':
    os.chdir('..')

os.system('./clean.sh')

os.chdir("benchmark/output")

OUTPUT_FILE_NAME = "bench_out_append.txt"

# class MyTimeout(Exception):
#     pass

with open(OUTPUT_FILE_NAME, 'w') as f:
    pass

def append(text):
    with open(OUTPUT_FILE_NAME, 'a') as f:
        f.write(str(text))

# Parameters
# not used
RETRY_COOLDOWN = 10

bench_set_candidate = ['sas19', 'muapprox_first_order', 'muapprox_katsura', 'muapprox_iwayama']
nth_last_line = -1
# if len(sys.argv) != 2:
#     raise(ValueError("specify bench_set name (one of " + str(bench_set_candidate) + ")"))
# elif not sys.argv[1] in bench_set_candidate: 
#     raise(ValueError("illegal bench_set name (one of " + str(bench_set_candidate) + ")"))


parser = argparse.ArgumentParser(description='benchmarker.')
parser.add_argument('bench_set', metavar='bench_set', type=str, 
                    choices=bench_set_candidate,
                    help='bench set name')
parser.add_argument('--timeout', dest='timeout', action='store', type=int, default=60,
                    help='timeout')

args = parser.parse_args()
bench_set_name = args.bench_set
timeout = float(args.timeout)

kill_process_names = ["hflmc2", "main.exe", "z3", "hoice", "eld", "java"]
lists_path = './list.txt'
base_dir = '/opt/home2/git/muapprox/benchmark/hes/'
add_args = []

if bench_set_name == 'sas19':
    # rec-limit (koba-test)
    exe_path = '/opt/home2/git/muapprox/benchmark/run_sas19.sh'
    nth_last_line = [-1]    # 出力の最後から1行目と2行目のいずれかを結果と解釈
    BENCH_SET = 1
else:
    # memory_watchdog.py を実行するしておくこと！
    exe_path = '/opt/home2/git/muapprox/benchmark/run_' + bench_set_name + '.sh'
    nth_last_line = -3
    BENCH_SET = 6

# if BENCH_SET == 2:
#     # under development
#     lists_path = './list.txt'
#     base_dir = '/opt/home2/git/muapprox/converted/'
#     exe_path = '/opt/home2/git/muapprox/_build/default/bin/main.exe'
#     add_args = []
#     nth_last_line = -3
# # higher
# if BENCH_SET == 4:
#     # mora
#     lists_path = './list2.txt'
#     base_dir = '/opt/home2/git/hflmc2_mora/benchmark/inputs/higher_nonterminating/'
#     exe_path = '/opt/home2/git/hflmc2_mora/_build/default/bin/main.exe'
#     add_args = []
#     nth_last_line = -3
# if BENCH_SET == 5:
#     lists_path = './list2.txt'
#     base_dir = '/opt/home2/git/muapprox/benchmark/inputs/higher_nonterminating/'
#     exe_path = '/opt/home2/git/muapprox/_build/default/bin/main.exe'
#     add_args = []
#     nth_last_line = -3

def get_lines(text):
    return text.strip(' \n\r').split("\n")
    
def get_last_line(text, nth = nth_last_line):
    try:
        if BENCH_SET == 6:
            m = re.search(r'\n\[\[MAIN]] Verification Result:\n\s*(\w+)\n', text)
            if m == None:
                return ('other', '')
            status = m.group(1)
            
            m = re.search(r'\n(\(mode=.+\))\n', text)
            if m == None:
                return (status, '')
            info = m.group(1)
            return (status, info)
        else:
            stdout = get_lines(text)[nth]
            if 'invalid' in stdout:
                return ('invalid', '')
            elif 'valid' in stdout:
                return ('valid', '')
            elif 'unknown' in stdout:
                return ('unknown', '')
            elif 'fail' in stdout:
                return ('fail', '')
            else:
                return ('other', '')
    except IndexError:
        return ('other', 'info')
    
def preexec_fn():
    os.chdir('./')
    os.setsid()

def readfile(path):
    with open(path, 'r') as f:
        return f.read()
    
def run(cmd):
    time.sleep(3.0)
    
    st = time.perf_counter()
    elapsed = timeout
    timed_out = False
    try:
        _ = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=preexec_fn,encoding='utf8', timeout=timeout)
        ed = time.perf_counter()
        elapsed = ed - st
    except subprocess.TimeoutExpired:
        timed_out = True

    stdout = readfile("/tmp/stdout_1.txt")
    stderr = readfile("/tmp/stderr_1.txt")
    
    for name in kill_process_names:
        os.system('pkill ' + name)
        
    return stdout, elapsed, stderr, timed_out

def search_status_from_last(lines, max_lines = 10):
    for i_ in range(1, max_lines + 1):
        i = -i_
        if lines[i] == "invalid" or lines[i] == "valid" or lines[i] == "unknown" or lines[i] == "fail":
            return lines[i]
    
    return 'other'

def get_data(file):
    def get_1(mode):
        try:
            with open(mode + '.tmp', 'r') as f:
                [_, pid, iter_count, coe1, coe2, path, file_] = f.read().split(',')
                if os.path.basename(file) == os.path.basename(file_):
                    return {
                        "pid": int(pid),
                        "iter_count": int(iter_count),
                        "coe1": int(coe1),
                        "coe2": int(coe2),
                        "path": path,
                    }
                else:
                    return {}
        except:
            print("get_1")
            return {}
            
    def get_2(mode):
        try:
            fn = 'post_' + mode + ".tmp"
            with open(fn, 'rb') as f:
                json_str = subprocess.Popen(["jq", "-cs", "."], stdout=subprocess.PIPE, stdin=subprocess.PIPE).communicate(f.read())[0]
                data = json.loads(json_str.decode('utf-8'))
                if os.path.basename(file) != os.path.basename(data[0]["file"]):
                    data = {}
            
            os.remove(fn)
            
            return data
        except:
            print("get_2")
            return []
    
    data = {}
    data['prover'] = get_1('prover')
    data['disprover'] = get_1('disprover')
    
    data['prover_post'] = get_2('prover')
    data['disprover_post'] = get_2('disprover')
    
    
    return data

# stderr, stdout, result, info
def parse_stdout(full_stdout, stderr):
    result_data = {}
    
    if stderr is None:
        stderr = ''
    result_data['stderr'] = stderr
    
    if isinstance(nth_last_line, list):
        # fptproverのとき
        result_data['result'], result_data['info'] = search_status_from_last(get_lines(full_stdout)), ''
    else:
        result_data['result'], result_data['info'] = get_last_line(full_stdout)
    
    if result_data['result'] == 'other':
        result_data['stdout'] = full_stdout
        
    return result_data
    
def gen_cmd(exe_path, file):
    cmd_template = [exe_path]  # <option> <filename>
    
    # ags.append('--')
    for i, _ in enumerate(add_args):
        cmd_template.append(add_args[i])
        
    # if args.no_inline:
    # ags.append('--no-inlining')
    cmd_template.append(file)
    return cmd_template

def log_file(file):
    with open('current.txt', 'w') as f:
        f.write(    file)
    
results = []
def handle(exe_path, file):
    print("file: " + file)
    append({'file': file})
    log_file(file)
    
    cmd = gen_cmd(exe_path, file)
    stdout, t, stderr, timed_out = run(cmd)
    if not timed_out:
        result = parse_stdout(stdout, stderr)
    else:
        if 1 == 0:  # trick for the type-checker
            stdout = 1
        result = {
            "result": "timeout",
            "info": '',
            "stdout": stdout,
            "stderr": stderr,
        }
        
    result['time'] = t
    if BENCH_SET == 6:
        result['data'] = get_data(file)
        
    append({'result': result})
    
    result['file'] = file
    results.append(result)

def get(r, key):
    if key in r:
        return r[key]
    return ''

def copy_without(dic, excludes):
    dic_ = {}
    for k, i in dic.items():
        if not k in excludes:
            dic_[k] = i
    
    return dic_

def to_table(data):
    lines = []
    for i, row in enumerate(data):
        lines.append(row['result'] + '\t' + str(row['time']) + '\n')
    
    return lines
    
def main():
    print("START")
    pprint({
        "bench_set_name": bench_set_name,
        "timeout": timeout,
        "lists_path": lists_path,
        "base_dir": base_dir,
        "exe_path": exe_path,
        "add_args": add_args,
        "nth_last_line": nth_last_line,
        "kill_process_names": kill_process_names,
    })
    
    with open(lists_path) as f:
        files = f.read().strip('\n').split('\n')
    
    for file in files:
        handle(exe_path, os.path.join(base_dir, file))
        
        with open('bench_out_full.txt', 'w') as f:    
            f.write(json.dumps(results, indent=2))
        
        # with open('bench_out_summary.txt', 'w') as f:
        #     f.write(json.dumps([copy_without(r, ['stdout', 'prover_post', 'disprover_post']) for r in results], indent=2))

        with open(OUTPUT_FILE_NAME + '_table.txt', 'w') as f:
            f.writelines(to_table(results))
    print("FINISHED")
    
main()
