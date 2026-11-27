# Print Rv64mc modules (excluding Gen) in topological import order, from the root module Rv64mc.
import os, re, sys
root = sys.argv[1]  # formal/rv64mc
def path(m): return os.path.join(root, *m.split('.')) + '.lean'
seen, order = set(), []
def visit(m):
    if m in seen: return
    seen.add(m)
    p = path(m)
    if not os.path.exists(p): return
    for line in open(p):
        r = re.match(r'\s*(?:public\s+)?import\s+(?:all\s+)?(Rv64mc[\w.]*)', line)
        if r: visit(r.group(1))
    if not m.startswith('Rv64mc.Gen'): order.append(m)
sys.setrecursionlimit(100000)
import glob
for f in sorted(glob.glob(os.path.join(root,'Rv64mc','**','*.lean'), recursive=True)):
    m=os.path.relpath(f,root)[:-5].replace(os.sep,'.')
    if not m.startswith('Rv64mc.Gen'): visit(m)
print('\n'.join(order))
