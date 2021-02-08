import os
import time

def get_physical_memory_size_in_gib():
    mem_bytes = os.sysconf('SC_PAGE_SIZE') * os.sysconf('SC_PHYS_PAGES')
    return mem_bytes / (1024.**3)
    
PROCESS_NAME = 'main.exe'
THRESHOLD = 11.0 / get_physical_memory_size_in_gib() * 100

def get_memory_usage(process_name):
    command = "top -b -n 1 -o \"%MEM\" -w | grep " + process_name + " | head -n 1 | awk '{print $1, $10}' > _result.tmp"
    os.system(command)
    try:
        with open('_result.tmp', 'r') as f:
            text = f.read()
    except:
        return get_memory_usage(process_name)
    
    data = text.split(' ')
    if len(data) < 2:
        return (-1, 0.0)
    
    return (int(data[0]), float(data[1]))

def show_info():
    try:
        with open("benchmark/output/current.txt", 'r') as f:
            bench = os.path.basename(f.read())
        
        return bench
    except:
        return ''
    
while True:
    (pid, usage) = get_memory_usage(PROCESS_NAME)
    if pid != -1 and usage > THRESHOLD:
        os.system("kill " + str(pid))
        print("Kiled!! (bench: " + show_info() + ")")
    
    time.sleep(1)
