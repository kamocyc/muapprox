import sys
# not_symbol = '!'
not_symbol = 'NOT '
text = sys.argv[1]  # e.g. "called, done, explore"
xs = [ t.strip() for t in text.split(",") ]

ls = []
for i, x in enumerate(xs):
    ls.append("(" + ' && '.join([ (not_symbol if i != i_ else "") + x_ for i_, x_ in enumerate(xs) ]) + ")")
    
print('(G(' + ' || '.join(ls) + "))")