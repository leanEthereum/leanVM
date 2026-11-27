import re, sys, os, glob, json, collections
root = sys.argv[1]
gen = os.path.join(root, 'Rv64mc/Gen')
idx = {}  # module -> (index, instrs, key)
for line in open(os.path.join(gen,'index.tsv')).read().splitlines()[1:]:
    mod, i, addr, n, sym, key, link = line.split('\t')
    idx[mod] = (int(i), int(n), key)
byi = {v[0]: k for k, v in idx.items()}
# link modules: namespace Rv64mc.Gen.<Mod> ... «field» := ⟨Idx.<Mod2>, ...⟩
calls = collections.defaultdict(set)
for f in glob.glob(os.path.join(gen,'Link','**','*.lean'), recursive=True):
    cur = None
    for line in open(f):
        m = re.match(r'namespace Rv64mc\.Gen\.(\S+)', line)
        if m: cur = m.group(1); continue
        m = re.search(r'«\w+» := ⟨Idx\.(\S+?),', line)
        if m and cur: calls[cur].add(m.group(1))
# loops: backward gotos/conds in template body
loops = {}
for mod in idx:
    p = os.path.join(gen,'Tmpl', *mod.split('.')) + '.lean'
    if not os.path.exists(p): loops[mod] = None; continue
    txt = open(p).read()
    labels = {}
    instrs = re.findall(r'LinstrR\.(\w+)([^\n]*)', txt)
    back = 0
    for k,(kind, rest) in enumerate(instrs):
        if kind == 'Llabel':
            m = re.search(r'\) (\d+)', rest); labels[int(m.group(1))] = k
    for k,(kind, rest) in enumerate(instrs):
        if kind in ('Lgoto','Lcond'):
            m = re.search(r'(\d+)\]?,?\s*$', rest.strip().rstrip(','))
            nums = re.findall(r'(\d+)\)?,?$', rest.strip())
            m = re.search(r'(\d+)\s*\)?\]?,?$', rest.strip())
            if m:
                l = int(m.group(1))
                if l in labels and labels[l] <= k: back += 1
    loops[mod] = back
# reachable from Main
reach = set(); st = ['Main']
while st:
    x = st.pop()
    if x in reach: continue
    reach.add(x); st.extend(calls.get(x, ()))
# SCC (Tarjan)
sys.setrecursionlimit(10000)
index = {}; low = {}; stack=[]; on=set(); sccs=[]; c=[0]
def sc(v):
    index[v]=low[v]=c[0]; c[0]+=1; stack.append(v); on.add(v)
    for w in calls.get(v,()):
        if w not in reach: continue
        if w not in index: sc(w); low[v]=min(low[v],low[w])
        elif w in on: low[v]=min(low[v],index[w])
    if low[v]==index[v]:
        comp=[]
        while True:
            w=stack.pop(); on.discard(w); comp.append(w)
            if w==v: break
        sccs.append(comp)
for v in sorted(reach): 
    if v not in index: sc(v)
# depth (height): leaves = 0
height = {}
for comp in sccs:  # tarjan emits in reverse topological (callees first)
    h = 0
    for v in comp:
        for w in calls.get(v,()):
            if w in reach and w not in comp: h = max(h, height[w]+1)
    for v in comp: height[v] = h
out = []
for comp in sccs:
    for v in comp:
        out.append(dict(mod=v, idx=idx[v][0], n=idx[v][1], key=idx[v][2], h=height[v], loops=loops[v],
                        rec=len(comp)>1 or v in calls.get(v,()), callees=sorted(calls.get(v,()))))
json.dump(out, open(sys.argv[2],'w'), indent=1)
print('reachable', len(reach), 'of', len(idx), 'instrs', sum(idx[v][1] for v in reach))
byh = collections.defaultdict(list)
for o in out: byh[o['h']].append(o)
for h in sorted(byh):
    print(h, len(byh[h]), sum(o['n'] for o in byh[h]), 'loops', sum(1 for o in byh[h] if o['loops']))
print('recursive', [o['key'] for o in out if o['rec']])
