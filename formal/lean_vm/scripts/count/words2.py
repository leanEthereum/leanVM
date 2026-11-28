"""Context-sensitive static words: constants propagated into callees through their argument cells; runtime counts
from a callback `rt(f, kind, off, stack)`; dispatches at a chosen arm (`pick(f, i, callees, stack)`) or their max."""
import pickle, re, sys
from lowered import gpow_table
G = gpow_table(1 << 21)
fns = pickle.load(open('fns.pkl', 'rb'))
PAD = 15
SET = re.compile(r'Set \{ o: (\d+), k: Const\(E \{ c0: (\d+), c1: (\d+) \}\) \}')
MUL = re.compile(r'Mul \{ a: (\d+), b: (\d+), c: (\d+) \}')
COPY = re.compile(r'Copy \{ src: (\d+), one: (\d+), dst: (\d+) \}')
SOLVE = re.compile(r'Solve \{ x: (\d+), b: (\d+), c: (\d+) \}')
DEREF = re.compile(r'Deref \{ o1: (\d+), o2: (\d+), o3: (\d+), mode: Cell \}')
JUMP = re.compile(r'Jump \{ oc: (\d+), od: (\d+), of: (\d+) \}')
for f in fns.values():
    ops = []
    for op, _ in f['code']:
        m = SET.match(op)
        if m: ops.append(('set', int(m.group(1)), G.get(int(m.group(2))) if int(m.group(3)) == 0 else None)); continue
        m = MUL.match(op)
        if m: ops.append(('mul',) + tuple(map(int, m.groups()))); continue
        m = COPY.match(op)
        if m: ops.append(('copy', int(m.group(1)), int(m.group(3)))); continue
        m = SOLVE.match(op)
        if m: ops.append(('solve',) + tuple(map(int, m.groups()))); continue
        m = DEREF.match(op)
        if m: ops.append(('deref',) + tuple(map(int, m.groups()))); continue
        m = JUMP.match(op)
        if m: ops.append(('jump',) + tuple(map(int, m.groups()))); continue
        ops.append(('other',))
    f['ops'] = ops
    f['hmap'] = dict(f['hints'])
def known_cells(f, env):
    """Cells of f whose value is one g-power on every path, given the argument cells `env`."""
    ops = fns[f]['ops']
    known = dict(env)
    for _ in range(3):
        cand = {}
        def add(c, v): cand.setdefault(c, set()).add(v)
        for op in ops:
            if op[0] == 'set': add(op[1], op[2])
            elif op[0] == 'mul':
                a, b, c = op[1:]
                add(c, known[a] + known[b] if a in known and b in known and known[a] is not None and known[b] is not None else None)
            elif op[0] == 'copy': add(op[2], known.get(op[1]))
            elif op[0] == 'solve':
                x, b, c = op[1:]
                add(x, known[c] - known[b] if c in known and b in known and None not in (known[c], known[b]) else None)
        new = dict(env)
        for c, vs in cand.items():
            if c in env: continue
            if len(vs) == 1 and None not in vs: new[c] = next(iter(vs))
        if new == known: break
        known = new
    return known
def call_args(f, i, ptr):
    """The callee's argument cells written from f's cells after the frame hint at i: {callee cell: f cell}."""
    ops = fns[f]['ops']; out = {}
    for op in ops[i:]:
        if op[0] == 'deref' and op[1] == ptr: out.setdefault(op[2], op[3])
        if op[0] == 'jump' and op[3] == ptr: break
    return out
UNRES = {}
def M(f, env, rt, pick=None, stack=(), log=None, skip=None):
    known = known_cells(f, env)
    tot = 0
    def val(kind, off):
        if off in known: return known[off]
        v = rt(f, kind, off, stack) if rt else None
        if v is None:
            UNRES[(f, kind, off)] = UNRES.get((f, kind, off), 0) + 1; return 0
        return v
    def sub(g, i, ptr):
        a = call_args(f, i, ptr)
        genv = {k: known[s] for k, s in a.items() if s in known}
        return M(g, genv, rt, pick, stack + ((f, i),), log, skip)
    for i, hs in fns[f]['hints']:
        for h in hs:
            if skip and skip(f, h, stack): continue
            if h[0] == 'frame':
                g = h[2]; c = fns[g]['frame'] + (PAD if fns[g]['keccak'] else 0) + sub(g, i, h[1])
            elif h[0] == 'arm':
                ch = pick(f, i, h[3], stack, known.get(h[2])) if pick else None
                if ch is None: ch = range(len(h[3]))
                c = (PAD if any(fns[g]['keccak'] for g in h[3]) else 0) + max(fns[h[3][k]]['frame'] + sub(h[3][k], i, h[1]) for k in ch)
            elif h[0] == 'buf': c = h[2]
            elif h[0] == 'dyn': c = val('dyn', h[2])
            elif h[0] == 'loop':
                _, ptr, g, n, bound, tail = h
                k = n - 1 if n is not None else max(val('loop', bound[0]) - bound[1], 0)
                body = sub(g, i, ptr) if k else 0
                c = fns[g]['frame'] * k + tail + (PAD if fns[g]['keccak'] else 0) + k * body
            if log is not None: log.append((len(stack), f, i, h[0], h[2] if h[0] != 'arm' else h[3][0], c))
            tot += c
    return tot

OPS = ['xor', 'mul', 'set', 'deref', 'jump', 'keccak']
def opk(op):
    h = op.split(' ', 1)[0]
    return {'Xor': 0, 'Mul': 1, 'Solve': 1, 'Copy': 1, 'Set': 2, 'Deref': 3, 'Slot': 3, 'Jump': 4, 'Keccak': 5}[h]
for f in fns.values():
    v = [0] * 6
    for op, _ in f['code']: v[opk(op)] += 1
    f['opv'] = v
def C(f, env, rt, pick=None, stack=(), skip=None):
    """Instructions by table, every instruction of every body counted (an upper bound on the rows)."""
    known = known_cells(f, env)
    tot = list(fns[f]['opv'])
    def add(v, k=1):
        for j in range(6): tot[j] += k * v[j]
    def val(kind, off):
        if off in known: return known[off]
        v = rt(f, kind, off, stack) if rt else None
        if v is None:
            UNRES[(f, kind, off)] = UNRES.get((f, kind, off), 0) + 1; return 0
        return v
    def sub(g, i, ptr):
        a = call_args(f, i, ptr)
        genv = {k: known[s] for k, s in a.items() if s in known}
        return C(g, genv, rt, pick, stack + ((f, i),), skip)
    for i, hs in fns[f]['hints']:
        for h in hs:
            if skip and skip(f, h, stack): continue
            if h[0] == 'frame': add(sub(h[2], i, h[1]))
            elif h[0] == 'arm':
                ch = pick(f, i, h[3], stack, known.get(h[2])) if pick else None
                if ch is None: ch = range(len(h[3]))
                vs = [sub(h[3][k], i, h[1]) for k in ch]
                for j in range(6): tot[j] += max(v[j] for v in vs)
            elif h[0] == 'loop':
                _, ptr, g, n, bound, tail = h
                k = n - 1 if n is not None else max(val('loop', bound[0]) - bound[1], 0)
                if k: add(sub(g, i, ptr), k)
    return tot
