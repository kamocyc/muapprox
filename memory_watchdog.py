import os
import time

def get_physical_memory_size_in_gib():
    mem_bytes = os.sysconf('SC_PAGE_SIZE') * os.sysconf('SC_PHYS_PAGES')
    return mem_bytes / (1024.**3)
    
PROCESS_NAME = 'main.exe'
THRESHOLD = 1.5 / get_physical_memory_size_in_gib()

def get_memory_usage(process_name):
    command = "top -b -n 1 -o \"%MEM\" | grep " + process_name + " | head -n 1 | awk '{print $1, $10}' > _result.tmp"
    os.system(command)
    with open('_result.tmp', 'r') as f:
        text = f.read()
    
    data = text.split(' ')
    if len(data) < 2:
        return (-1, 0.0)
    
    return (int(data[0]), float(data[1]))

def fname():
    try:
        with open("benchmark/output/current.txt", 'r') as f:
            return f.read()
    except:
        return ''
    
while True:
    (pid, usage) = get_memory_usage(PROCESS_NAME)
    if pid != -1 and usage > THRESHOLD:
        os.system("kill " + str(pid))
        print("Kiled!! (file: " + os.path.basename(fname()) + ", pid: " + str(pid) + ")")
    
    time.sleep(1)
