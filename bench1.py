import os
import subprocess
import signal   
import time

# Parameters
# not used
RETRY_COOLDOWN = 10

timeout = 180

nth_last_line = -1
BENCH_SET = 4

if BENCH_SET == 1:
    # rec-limit
    lists_path = './list.txt'
    base_dir = '/opt/home2/git/fptprove_muarith/benchmarks/muArith/'
    exe_path = '/opt/home2/git/fptprove_muarith/_build/default/bin/main.exe'
    add_args = ['--algorithm rec-limit']
    nth_last_line = -1    # 出力の最後から1行目を結果と解釈

if BENCH_SET == 2:
    # cegis
    lists_path = './list.txt'
    base_dir = '/opt/home2/git/fptprove_muarith/benchmarks/muArith/'
    exe_path = '/opt/home2/git/fptprove_muarith/_build/default/bin/main.exe'
    add_args = []
    nth_last_line = -1

if BENCH_SET == 3:
    # unde development
    lists_path = './list.txt'
    base_dir = '/opt/home2/git/fptprove_muarith/converted/'
    exe_path = '/opt/home2/git/muapprox/_build/default/bin/main.exe'
    add_args = []
    nth_last_line = -3

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
    
    

def get_last_line(text, nth = nth_last_line):
    try:
        return text.strip(' \n\r').split("\n")[nth]
    except IndexError:
        return text.strip(' \n\r')
    
def preexec_fn():
    os.chdir('./')
    os.setsid()
    
def run(cmd):
    st = time.perf_counter()
    with subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, preexec_fn=preexec_fn) as p:
        try:
            output, _ = p.communicate(timeout=timeout)
            ed = time.perf_counter()
            elapsed = ed - st
            return output, elapsed
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except:
                pass
            raise
        
def parse_stdout(stdout):
    # ?
    print({'full': stdout})
    stdout = get_last_line(stdout)
    print({'stdout': stdout})
    result_data = dict()
    result_data['result'] = 'invalid' if 'invalid' in stdout else 'valid' if 'valid' in stdout else 'fail'
    # print(result_data['result'])
    # print(stdout)
    return result_data
    
def callback(file, result):
    # print(file)
    pass

def gen_cmd(exe_path, file):
    cmd_template = exe_path + ' {} {}'  # <option> <filename>
    
    # args = cfg.args
    ags = []
    # ags.append('--')
    for i, _ in enumerate(add_args):
        ags.append(add_args[i])
    # if args.no_inline:
    # ags.append('--no-inlining')

    ag = ' '.join(ags)
    return cmd_template.format(ag, file)

results = []
def handle(exe_path, file, parser, callback, retry=0):
    print({'file': file})
    
    cmd = gen_cmd(exe_path, file)
    try:
        stdout, t = run(cmd)
        stdout = stdout.decode('utf-8')
        result = parser(stdout)
        result['time'] = t
    except subprocess.TimeoutExpired:
        result = {'ok': False, 'error': 'timeout'}
        result['time'] = timeout
    
    print({'result': result})
    
    if 'result' not in result:
        result['result'] = 'fail'
    if result['result'] == 'fail' and retry > 0:
        time.sleep(RETRY_COOLDOWN)
        handle(file, parser, callback, retry - 1)
    else:
        result['file'] = file
        callback(file, result)
        results.append(result)

def main():
    with open(lists_path) as f:
        files = f.read().strip('\n').split('\n')
    
    for file in files:
        handle(exe_path, os.path.join(base_dir, file), parse_stdout, callback=callback)
    
    print(results)            
    
main()
