from pprint import pprint
import json
import os
import subprocess
import time
import re
import argparse
import glob

OUTPUT_FILE_NAME = "0bench_out_append.txt"

def append(text):
    with open(OUTPUT_FILE_NAME, 'a') as f:
        f.write(str(text))

def is_process_running(process_name):
    os.system("ps -ef | grep \"" + process_name + "\" | grep -v grep | awk '{ print $2 }' > __result2.tmp")
    try:
        with open('__result2.tmp', 'r') as f:
            text = f.read().strip()
    except:
        return is_process_running(process_name)
    
    return text != ''

def prepare():
    global timeout, lists_path, base_dir, exe_path, add_args
    
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

    with open(OUTPUT_FILE_NAME, 'w') as f:
        pass

    BACKEND_SOLVER_CANDIDATE = ['muapprox_first_order', 'muapprox_katsura', 'muapprox_iwayama', 'muapprox_suzuki', 'muapprox_katsura_replacer', 'muapprox_mochi']

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
    
    lists_path = os.path.join(benchmark_dir, 'file_list/' + benchmark + '.txt')    # lists_path
    base_dir = os.path.join(benchmark_dir, 'inputs')                               # base_dir
    exe_path = os.path.join(benchmark_dir, 'run_' + backend_solver_name + '.sh')   # exe_path
    
    print("START")
    pprint({
        "backend_solver_name": backend_solver_name,
        "timeout":    timeout,
        "lists_path": lists_path,
        "base_dir":   base_dir,
        "exe_path":   exe_path,
        "add_args":   add_args,
    })
    
    return
    
def extract_result(text):
    try:
        m = re.search(r'\n\[\[MAIN]] Verification Result:\n\s*(\w+)\n', text)
        if m == None:
            return ('other', '')
        status = m.group(1)
        
        m = re.search(r'\n(\(mode=.+\))\n', text)
        if m == None:
            return (status, '')
        info = m.group(1)
        return (status, info)
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
    print(cmd, flush=True)
    
    st = time.perf_counter()
    elapsed = timeout
    timed_out = False
    result = subprocess.run(["timeout", str(timeout)] + cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=preexec_fn, encoding='utf8')
    if result.returncode == 124:
        timed_out = True
    else:
        ed = time.perf_counter()
        elapsed = ed - st

    stdout = readfile("/tmp/stdout_1.txt")
    stderr = readfile("/tmp/stderr_1.txt")
    
    os.system('../../killp.sh')
    
    return stdout, elapsed, stderr, timed_out

def get_data(file, result):
    def get_file_pattern(prefix, mode):
        return prefix + "_" + os.path.splitext(os.path.basename(file))[0] + "_" + mode + "_*.tmp"
    
    def load_jsons_data(filename):
        with open(filename, 'rb') as f:
            json_str = subprocess.Popen(["jq", "-cs", "."], stdout=subprocess.PIPE, stdin=subprocess.PIPE).communicate(f.read())[0]
            return json.loads(json_str.decode('utf-8'))
    
    
    def get(mode, pre_or_post):
        # try:
            files = glob.glob(get_file_pattern(pre_or_post, mode))
            if files == []:
                print("get (" + pre_or_post + "): not found (" + mode + ")")
                return []
            if len(files) > 1:
                print("WARN 1")
            
            print("file: " + files[0])
            
            data = load_jsons_data(files[0])
            os.remove(files[0])
            return data
        
    def get_post_merged(mode, d):
        # try:
            files = glob.glob(get_file_pattern("post_merged", mode))
            res = []
            for file2 in files:
                print("file: " + file2)
                data = load_jsons_data(file2)
                assert(len(data) == 1)
                res.append(data[0])
                os.remove(file2)
        
            if res == []:
                {}
            else:
                result2 = result['result']
                match = (result2 == 'invalid' and mode == 'disprover') or (result2 == 'valid' and mode == 'prover')
                cs = [r["iter_count"] for r in res]
                if max(cs) > d['iter_count'] or (match and max(cs) != d['iter_count']):
                    print(d['iter_count'])
                    print(max(cs))
                    print("WARN 2")
                    
                for i in range(max(cs)):
                    if cs.count(i+1) != 1:
                        print("WARN 3")
                
                return {
                    "t_count": res[0]["t_count"],
                    "s_count": res[0]["s_count"],
                    "elapsed_all": sum([c["elapsed_all"] for c in res]),
                }
            
    data = {}
    data['pre_prover'] = get('prover', 'pre')
    data['pre_disprover'] = get('disprover', 'pre')
    
    data['post_prover'] = get('prover', 'post')
    data['post_disprover'] = get('disprover', 'post')
    
    data['post_merged_prover'] = get_post_merged('prover', data['pre_prover'][-1])
    data['post_merged_disprover'] = get_post_merged('disprover', data['pre_disprover'][-1])
    
    return data

# stderr, stdout, result, info
def parse_stdout(full_stdout, stderr):
    result_data = {}
    
    if stderr is None:
        stderr = ''
    
    result_data['stderr'] = stderr
    result_data['result'], result_data['info'] = extract_result(full_stdout)
    
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
    print("file: " + file, flush=True)
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
    
    # print({'result': result})
    result['time'] = t
    result['data'] = get_data(file, result)
        
    append({'result': result})
    
    result['file'] = file
    results.append(result)

def to_table(data):
    lines = []
    for _, row in enumerate(data):
        lines.append(row['result'] + '\t' + str(row['time']) + '\n')
    
    return lines
    
def main():    
    with open(lists_path) as f:
        files = [line for line in [l.strip() for l in f.readlines()] if line != '' and line[0] != '#']
    
    for file in files:
        handle(exe_path, os.path.join(base_dir, file))
        
        with open('0bench_out_full.txt', 'w') as f:    
            f.write(json.dumps(results, indent=2))

        with open(OUTPUT_FILE_NAME + '_table.txt', 'w') as f:
            f.writelines(to_table(results))
    
    print("FINISHED")
    
    os.system("""
        jq -r '[.[] | {
            file: .file,
            result: .result,
            time: .time,
            prove_iter_count: .data.pre_prover[-1].iter_count,
            disprove_iter_count: .data.pre_disprover[-1].iter_count,
            prover_t_count: .data.pre_prover[-1].t_count,
            prover_s_count: .data.pre_prover[-1].s_count,
            disprover_t_count: .data.pre_disprover[-1].t_count,
            disprover_s_count: .data.pre_disprover[-1].s_count,
            prover_elapsed_all: .data.post_merged_prover.elapsed_all,
            disprover_elapsed_all: .data.post_merged_disprover.elapsed_all}]
            | .[] | "\\(.prove_iter_count)\t\\(.disprove_iter_count)\t\\(.prover_t_count)\t\\(.prover_s_count)\t\\(.disprover_t_count)\t\\(.disprover_s_count)\t\\(.prover_elapsed_all)\t\\(.disprover_elapsed_all)"' 0bench_out_full.txt > """ + OUTPUT_FILE_NAME + "_iter_count.txt")
    
    os.system("paste " + OUTPUT_FILE_NAME + '_table.txt' + ' ' + OUTPUT_FILE_NAME + "_iter_count.txt > " + OUTPUT_FILE_NAME + "_summary.txt")
    
    # prove_iter_count,disprove_iter_count,prover_t_count,prover_s_count,disprover_t_count,disprover_s_count,prover_elapsed_all,disprover_elapsed_all
    print("time: " + os.path.join(os.getcwd(), OUTPUT_FILE_NAME + "_summary.txt"))
    print("list: " + os.path.join(os.getcwd(), lists_path))
    print("full: " + os.path.join(os.getcwd(), "0bench_out_full.txt"))

prepare()

main()
