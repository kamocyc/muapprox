import sys
import uuid
import tempfile
import os

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

if len(sys.argv) != 3:
    print('Error: illegal number of arguments')
    sys.exit(1)
    
target_name = sys.argv[1]
input_filename = sys.argv[2]

replacement_config = {
    'array_plus_loop_easy': [
        ('\\/ Main s3 ar3', '\\/ Main x y (x+y) s3 ar3'),
        ('Main t ar k =v', 'Main x_ y_ xy_ t ar k =v'),
        ('Loop recLoop 0 ar k', 'Loop recLoop x_ y_ xy_ 0 ar k'),
        ('Loop recLoop i ar k =v', 'Loop recLoop x_ y_ xy_ i ar k =v'),
        ('\\/ Loop (recLoop - 1) (i + 1)', '\\/ Loop (recLoop - 1) x_ y_ xy_ (i + 1)')
    ],
    'list_plus_loop_easy': [
        ('\\/ Loop recLoop 0', '\\/ Loop recLoop x y (x+y) 0'),
        ('Loop recLoop i', 'Loop recLoop x_ y_ xy_ i'),
        ('\\/ Loop (recLoop - 1) (i + 1)', '\\/ Loop (recLoop - 1) x_ y_ xy_ (i + 1)'),
    ],
    'mutual_fixpoints': [
        ('\\/ M s', '\\/ M x s'),
        ('M t f =v', 'M x t f =v'),
        ('Outer t fx =v', 'Outer x t fx =v'),
        ('Outer s f', 'Outer x s f'),
        ('\\/ Repeat recRepeat s', '\\/ Repeat recRepeat (x + y) s'),
        ('Repeat recRepeat t fy =v', 'Repeat recRepeat xy t fy =v'),
        ('\\/ Outer s (Neg fy)', '\\/ Outer (1 - xy) s (Neg fy)'),
        ('\\/ Repeat (recRepeat - 1) s', '\\/ Repeat (recRepeat - 1) (xy - 1) s')
    ]
}

if not target_name in replacement_config:
    print('Error: illegal target name')
    sys.exit(1)

try:
    with open(input_filename, 'r') as f:
        buf = "".join(f.readlines())
except FileNotFoundError:
    print("Error: file \"" + input_filename + "\" not found")
    sys.exit(1)

sources = [s for s, _ in replacement_config[target_name]]
targets = [s for _, s in replacement_config[target_name]]

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

