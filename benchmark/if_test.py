# (p => a) /\ (not p => b)
# (not p \/ a) /\ (p \/ b)

# not if1
# (p /\ not a) \/ (not p /\ not b)

def if1(p, a, b):
    return ((not p) or a) and (p or b)

def if3(p, a, b):
    return not (((not p) or a) and (p or b))

def if4(p, a, b):
    return (p and (not a)) or ((not p) and (not b))

# p1の否定=
def if5(p, a, b):
    return ((not p) or (not a)) and (p or (not b))
    
# (p /\ a) \/ (not p /\ b)
def if2(p, a, b):
    return (p and a) or ((not p) and b)

def tb(n):
    if n == 0:
        return False
    else:
        return True
        
for p in range(2):
    for a in range(2):
        for b in range(2):
            p = tb(p)
            a = tb(a)
            b = tb(b)
            print({
                "p": p,
                "a": a,
                "b": b,
                "if1": if1(p, a, b),
                "if2": if2(p, a, b),
                "if3": if3(p, a, b),
                "if4": if4(p, a, b),
                "if5": if5(p, a, b),
            })
    