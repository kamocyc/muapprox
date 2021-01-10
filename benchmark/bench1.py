from pprint import pprint
import os
import subprocess
import signal   
import time
import re

if os.path.isdir('benchmark'):
    os.chdir('benchmark')
os.chdir("output")

OUTPUT_FILE_NAME = "bench_out_append.txt"

class MyTimeout(Exception):
    pass

with open(OUTPUT_FILE_NAME, 'w') as f:
    pass

def append(text):
    with open(OUTPUT_FILE_NAME, 'a') as f:
        f.write(str(text))

# Parameters
# not used
RETRY_COOLDOWN = 10

timeout = 180

nth_last_line = -1
BENCH_SET = 6

kill_process_names = []
use_file_for_output = True

if BENCH_SET == 1:
    # rec-limit (koba-test)
    lists_path = './list.txt'
    base_dir = '/opt/home2/git/fptprove_muarith/benchmarks/hes/'
    exe_path = '/opt/home2/git/muapprox/benchmark/run_command.sh'
    add_args = []
    nth_last_line = [-1]    # 出力の最後から1行目と2行目のいずれかを結果と解釈
    kill_process_names = ["z3", "main.exe"]
    use_file_for_output = True

# if BENCH_SET == 2:
#     # under development
#     lists_path = './list.txt'
#     base_dir = '/opt/home2/git/muapprox/converted/'
#     exe_path = '/opt/home2/git/muapprox/_build/default/bin/main.exe'
#     add_args = []
#     nth_last_line = -3

# higher
if BENCH_SET == 4:
    # mora
    lists_path = './list2.txt'
    base_dir = '/opt/home2/git/hflmc2_mora/benchmark/inputs/higher_nonterminating/'
    exe_path = '/opt/home2/git/hflmc2_mora/_build/default/bin/main.exe'
    add_args = []
    nth_last_line = -3
    
if BENCH_SET == 5:
    lists_path = './list2.txt'
    base_dir = '/opt/home2/git/muapprox/benchmark/inputs/higher_nonterminating/'
    exe_path = '/opt/home2/git/muapprox/_build/default/bin/main.exe'
    add_args = []
    nth_last_line = -3

if BENCH_SET == 6:
    # memory_watchdog.py を実行するしておくこと！
    lists_path = './list.txt'
    # lists_path = './list_timeout.txt'
    base_dir = '/opt/home2/git/muapprox/benchmark/hes/'
    # exe_path = '/opt/home2/git/muapprox/_build/default/bin/main.exe'
    exe_path = '/opt/home2/git/muapprox/benchmark/run_command2.sh'
    add_args = []
    #add_args = ['--hes']
    #add_args = ['--hes', '--solver', 'iwayama']
    # add_args = ['--hes', '--first-order-solver']
    kill_process_names = ["hflmc2", "main.exe", "z3", "hoice", "eld"]
    nth_last_line = -3

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
                return ('other', '')
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
            # "[[MAIN]] Verification Result:\n  invalid\nProfiling:\n  total: 5.166029 sec\n(mode=disprover, iter_count=1, coe1=1, coe2=1)"
    except IndexError:
        return ('other', 'info')
    
def preexec_fn():
    os.chdir('./')
    os.setsid()

def readfile(path):
    with open(path, 'r') as f:
        return f.read()
    
def run(cmd):
    st = time.perf_counter()
    try:
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=preexec_fn,encoding='utf8', timeout=timeout)
        ed = time.perf_counter()
        elapsed = ed - st
        if use_file_for_output:
            stdout = readfile("/tmp/stdout_1.txt")
            stderr = readfile("/tmp/stderr_1.txt")
        else:
            stdout = r.stdout
            stderr = r.stderr
            
        return stdout, elapsed, stderr
    except subprocess.TimeoutExpired as e:
        if use_file_for_output:
            stdout = readfile("/tmp/stdout_1.txt")
            stderr = readfile("/tmp/stderr_1.txt")
        else:
            stdout = e.stdout
            if stdout is None:
                stdout = ""
            
            stderr = e.stderr
            if stderr is None:
                stderr = ""
        
        # これが無いと、プロセスが残る
        os.system('pkill ' + os.path.basename(exe_path))
        for name in kill_process_names:
            os.system('pkill ' + name)
        
        raise MyTimeout({'stdout': stdout, 'timeout': timeout, 'stderr': stderr})

def search_status_from_last(lines, max_lines = 10):
    for i_ in range(1, max_lines + 1):
        i = -i_
        if lines[i] == "invalid" or lines[i] == "valid" or lines[i] == "unknown" or lines[i] == "fail":
            return lines[i]
    
    return 'other'
        
def parse_stdout(full_stdout, stderr):
    # ?
    # append({'full': full_stdout})
    result_data = dict()
    
    if stderr is None:
        stderr = ''
    
    result_data['stderr'] = stderr
    
    result_data['info'] = ''
    
    if isinstance(nth_last_line, list):
        # fptproverのとき
        lines = get_lines(full_stdout)
        stdout = search_status_from_last(lines)
        
        append({'stdout': stdout})
        
        if stdout != 'other':
            result_data['result'] = stdout
        else:
            if stderr is None:
                stderr = ''
            result_data['result'] = 'other'
            result_data['stdout'] = full_stdout
    else:
        result_data['result'], result_data['info'] = get_last_line(full_stdout)
        if result_data['result'] == 'other':
            result_data['stdout'] = full_stdout
        
    # append(result_data['result'])
    # append(stdout)
    return result_data
    
def callback(file, result):
    # append(file)
    pass

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
        f.write(file)
    
results = []
def handle(exe_path, file, parser, callback, retry=0):
    print("file: " + file)
    append({'file': file})
    log_file(file)
    
    cmd = gen_cmd(exe_path, file)
    try:
        stdout, t, stderr = run(cmd)
        result = parser(stdout, stderr)
        result['time'] = t
    except MyTimeout as e:
        result = {}
        result['result'] = 'timeout'
        result['stdout'] = e.args[0]['stdout']
        result['stderr'] = e.args[0]['stderr']
        result['time'] = e.args[0]['timeout']
    
    append({'result': result})
    
    # if 'result' not in result:
    #     result['result'] = 'fail'
    # if result['result'] == 'fail' and retry > 0:
    #     time.sleep(RETRY_COOLDOWN)
    #     handle(file, parser, callback, retry - 1)
    # else:
    result['file'] = file
    callback(file, result)
    results.append(result)

def get(r, key):
    if key in r:
        return r[key]
    return ''
    
def main():
    print("START")
    pprint({
        "lists_path": lists_path,
        "base_dir": base_dir,
        "exe_path": exe_path,
        "add_args": add_args,
        "nth_last_line": nth_last_line,
        "kill_process_names": kill_process_names,
        "use_file_for_output": use_file_for_output
    })
    
    with open(lists_path) as f:
        files = f.read().strip('\n').split('\n')
    
    for file in files:
        handle(exe_path, os.path.join(base_dir, file), parse_stdout, callback=callback)

    with open('bench_out_summary.txt', 'w') as f:            
        f.write(str([{'file': r['file'], 'info': get(r, 'info'), 'result': r['result'], 'time': r['time']} for r in results]))
    
    with open('bench_out_full.txt', 'w') as f:    
        f.write(str(results))
    
    print("FINISHED")
    
main()
