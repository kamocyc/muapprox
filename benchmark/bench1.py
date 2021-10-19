from pprint import pprint
import json
import os
import subprocess
import time
import re
import argparse
import glob

def is_process_running(process_name):
    os.system("ps -ef | grep \"" + process_name + "\" | grep -v grep | awk '{ print $2 }' > __result2.tmp")
    try:
        with open('__result2.tmp', 'r') as f:
            text = f.read().strip()
    except:
        return is_process_running(process_name)
    
    return text != ''

if not is_process_running("python3 memory_watchdog.py"):
    print('########################')
    print('Error: memory_watchdog.py IS NOT RUNNING')
    print('########################')
    exit(1)

# set path
if os.path.basename(os.getcwd()) == 'benchmark':
    os.chdir('..')

os.system('./clean.sh')
os.chdir("benchmark")

if not os.path.exists("output"):
    os.mkdir("output")

os.chdir("output")

OUTPUT_FILE_NAME = "0bench_out_append.txt"

with open(OUTPUT_FILE_NAME, 'w') as f:
    pass

def append(text):
    with open(OUTPUT_FILE_NAME, 'a') as f:
        f.write(str(text))

BACKEND_SOLVER_CANDIDATE = ['sas19', 'muapprox_first_order', 'muapprox_katsura', 'muapprox_iwayama', 'muapprox_suzuki', 'muapprox_katsura_replacer']

parser = argparse.ArgumentParser(description='benchmarker.')
parser.add_argument('backend_solver', metavar='backend_solver', type=str, 
                    choices=BACKEND_SOLVER_CANDIDATE,
                    help='backend solver name')
parser.add_argument('--timeout', dest='timeout', action='store', type=int, required=True,
                    help='timeout')
parser.add_argument('--benchmark', dest='benchmark', action='store', type=str, required=True,
                    help='benchmark set')
parser.add_argument('--pass-args', dest='pass_args', action='store', type=str,
                    help='additional arguments to pass them to the Hflz solver')
                    
KILL_PROCESS_NAMES = ["hflmc2", "main.exe", "muapprox_main.exe", "z3", "hoice", "eld", "java", "hflmc3.sh", "para_aux.sh", "sh", "hflmc"]
nth_last_line = -1

args = parser.parse_args()
backend_solver_name = args.backend_solver
timeout = float(args.timeout)
benchmark = args.benchmark
add_args = args.pass_args
if add_args == None:
    add_args = []
else:
    add_args = add_args.split(" ")

benchmark_dir = os.path.dirname(os.getcwd())
lists_path = os.path.join(benchmark_dir, 'file_list/' + benchmark + '.txt')
base_dir = os.path.join(benchmark_dir, 'inputs')

if backend_solver_name == 'sas19':
    # rec-limit (koba-test)
    exe_path = os.path.join(benchmark_dir, 'run_sas19.sh')
    nth_last_line = [-1]    # 出力の最後から1行目と2行目のいずれかを結果と解釈
    BENCH_SET = 1
else:
    # memory_watchdog.py を実行するしておくこと！
    exe_path = os.path.join(benchmark_dir, 'run_' + backend_solver_name + '.sh')
    nth_last_line = -3
    BENCH_SET = 6

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
    with open(path, 'r', errors='ignore') as f:
        return f.read()
    
def run(cmd):
    time.sleep(3.0)
    print("CMD: ")
    print(cmd)
    
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
    
    # for name in KILL_PROCESS_NAMES:
    #     os.system('killall -9 ' + name)
    os.system('../../killp.sh')
        
    return stdout, elapsed, stderr, timed_out

def search_status_from_last(lines, max_lines = 10):
    for i_ in range(1, max_lines + 1):
        i = -i_
        if lines[i] == "invalid" or lines[i] == "valid" or lines[i] == "unknown" or lines[i] == "fail":
            return lines[i]
    
    return 'other'

def get_data(file, result):
    def get_1(mode):
        try:
            with open(mode + '.tmp', 'r') as f:
                [_, pid, iter_count, coe1, coe2, path, file_, t_count, s_count] = f.read().split(',')
                if os.path.basename(file) == os.path.basename(file_):
                    return {
                        "pid": int(pid),
                        "iter_count": int(iter_count),
                        "coe1": int(coe1),
                        "coe2": int(coe2),
                        "path": path,
                        "t_count": int(t_count),
                        "s_count": int(s_count)
                    }
                else:
                    return {}
        except:
            print("get_1 (pre): not found (" + mode + ")")
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
            print("get_2 (post): not found (" + mode + ")")
            return []
    
    def get_3(mode, d):
        # try:
            files = glob.glob("output2_" + os.path.splitext(os.path.basename(file))[0] + "_" + mode + "_*_output2.tmp")
            res = []
            for file2 in files:
                print("file: " + file2)
                with open(file2, 'r') as f:
                    [_, pid, iter_count, coe1, coe2, file_, t_count, s_count, elapse_all] = f.read().split(',')
                    if os.path.basename(file) == os.path.basename(file_):
                        res.append({
                            "iter_count": int(iter_count),
                            "t_count": int(t_count),
                            "s_count": int(s_count),
                            "elapse_all": float(elapse_all),
                        })
                    else:
                        raise ValueError
            
            if res == []:
                {}
            else:
                result2 = result['result']
                match = (result2 == 'invalid' and mode == 'disprover') or  (result2 == 'valid' and mode == 'prover')
                cs = [r["iter_count"] for r in res]
                if max(cs) > d['iter_count'] or (match and max(cs) != d['iter_count']):
                    print(d['iter_count'])
                    print(max(cs))
                    raise ValueError
                    
                for i in range(max(cs)):
                    if cs.count(i+1) != 1:
                        raise ValueError
                return {
                    "t_count": res[0]["t_count"],
                    "s_count": res[0]["s_count"],
                    "elapse_all": sum([c["elapse_all"] for c in res]),
                }                    
        # except:
        #     print("get_3 (output2): not found (" + mode + ")")
        #     return {}
            
    data = {}
    data['prover'] = get_1('prover')
    data['disprover'] = get_1('disprover')
    
    data['prover_post'] = get_2('prover')
    data['disprover_post'] = get_2('disprover')
    
    data['prover_output2'] = get_3('prover', data['prover'])
    data['disprover_output2'] = get_3('disprover', data['disprover'])
    
    
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
    
    cmd_template.append(file)
    
    for _, add_arg in enumerate(add_args):
        cmd_template.append(add_arg)
    
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
    
    print({'result': result})
    result['time'] = t
    if BENCH_SET == 6:
        result['data'] = get_data(file, result)
        
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
        "backend_solver_name": backend_solver_name,
        "timeout": timeout,
        "lists_path": lists_path,
        "base_dir": base_dir,
        "exe_path": exe_path,
        "add_args": add_args,
        "nth_last_line": nth_last_line,
    })
    
    with open(lists_path) as f:
        files = [line for line in [l.strip() for l in f.readlines()] if line != '' and line[0] != '#']
    
    for file in files:
        handle(exe_path, os.path.join(base_dir, file))
        
        with open('0bench_out_full.txt', 'w') as f:    
            f.write(json.dumps(results, indent=2))
        
        # with open('0bench_out_summary.txt', 'w') as f:
        #     f.write(json.dumps([copy_without(r, ['stdout', 'prover_post', 'disprover_post']) for r in results], indent=2))

        with open(OUTPUT_FILE_NAME + '_table.txt', 'w') as f:
            f.writelines(to_table(results))
    print("FINISHED")
    
    os.system("""
        jq -r '[.[] | {
            file: .file,
            result: .result,
            time: .time,
            prove_iter_count: .data.prover.iter_count,
            disprove_iter_count: .data.disprover.iter_count,
            prove_iters: .data.prover_post | map({iter_index: .iter_count, time: .time}),
            disprove_iters: .data.disprover_post | map({iter_index: .iter_count, time: .time}),
            prover_t_count: .data.prover.t_count,
            prover_s_count: .data.prover.s_count,
            disprover_t_count: .data.disprover.t_count,
            disprover_s_count: .data.disprover.s_count,
            prover_elapse_all: .data.prover_output2.elapse_all,
            disprover_elapse_all: .data.disprover_output2.elapse_all}]
            | .[] | "\\(.prove_iter_count)\t\\(.disprove_iter_count)\t\\(.prover_t_count)\t\\(.prover_s_count)\t\\(.disprover_t_count)\t\\(.disprover_s_count)\t\\(.prover_elapse_all)\t\\(.disprover_elapse_all)"' 0bench_out_full.txt > """ + OUTPUT_FILE_NAME + "_iter_count.txt")
    
    os.system("paste " + OUTPUT_FILE_NAME + '_table.txt' + ' ' + OUTPUT_FILE_NAME + "_iter_count.txt > " + OUTPUT_FILE_NAME + "_summary.txt")
    
    # prove_iter_count,disprove_iter_count,prover_t_count,prover_s_count,disprover_t_count,disprover_s_count,prover_elapse_all,disprover_elapse_all
    print("time: " + os.path.join(os.getcwd(), OUTPUT_FILE_NAME + "_summary.txt"))
    print("list: " + os.path.join(os.getcwd(), lists_path))
    print("full: " + os.path.join(os.getcwd(), "0bench_out_full.txt"))
main()
