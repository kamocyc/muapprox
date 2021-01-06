import os
import time

PROCESS_NAME = 'main.exe'
THRESHOLD = 40.0

def get_memory_usage(process_name):
    command = "top -b -n 1 -o \"%MEM\" | grep " + process_name + " | head -n 1 | awk '{print $1, $10}' > _result.txt"
    os.system(command)
    with open('_result.txt', 'r') as f:
        text = f.read()
    
    data = text.split(' ')
    if len(data) < 2:
        return (-1, 0.0)
    
    return (int(data[0]), float(data[1]))

while True:
    (pid, usage) = get_memory_usage(PROCESS_NAME)
    if pid != -1 and usage > THRESHOLD:
        os.system("kill " + str(pid))
        print("Kiled!!")
    
    time.sleep(1)
