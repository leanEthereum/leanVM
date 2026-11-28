"""Rows by table along each function's costliest path: the lowered code's control flow (local jumps, inline
matches' jump tables, calls returning to the next instruction), each instruction one row of its table plus the
rows of what its hints call; a separate longest path per table and for the total."""
import re, sys
import words2 as w
fns = w.fns
LOCAL = re.compile(r'Set \{ o: (\d+), k: Local\((\d+)\) \}')
ENTRY = re.compile(r'Set \{ o: (\d+), k: Entry\("([^"]+)"\) \}')
SLOT = re.compile(r'Slot \{ x: (\d+), first: (\d+), dst: (\d+) \}')
TABLE = {}
for idx, (op, _) in enumerate(fns['__jump_tables']['code']):
    m = re.search(r'k: At\("([^"]+)", (\d+)\)', op)
    if m: TABLE[idx] = ('at', m.group(1), int(m.group(2))); continue
    m = re.search(r'k: Entry\("([^"]+)"\)', op)
    if m: TABLE[idx] = ('entry', m.group(1))
FIRSTS = sorted({int(SLOT.match(op).group(2)) for f in fns.values() for op, _ in f['code'] if op.startswith('Slot')})
def table_targets(first):
    nxt = next((x for x in FIRSTS if x > first), 10 ** 9)
    out = []; k = first
    while k < nxt and k in TABLE: out.append(TABLE[k]); k += 1
    return out
for f in fns.values():
    code = f['code']; n = len(code)
    loc = {}; ent = {}; slot = {}
    for i, (op, _) in enumerate(code):
        m = LOCAL.match(op)
        if m: loc.setdefault(int(m.group(1)), set()).add(int(m.group(2)))
        m = ENTRY.match(op)
        if m: ent[int(m.group(1))] = m.group(2)
        m = SLOT.match(op)
        if m: slot[int(m.group(3))] = int(m.group(2))
    consts = f['consts']
    succ = []
    for i, (op, _) in enumerate(code):
        m = w.JUMP.match(op)
        if not m:
            succ.append([i + 1] if i + 1 < n else []); continue
        oc, od, of = map(int, m.groups())
        cv = consts.get(oc)
        cz = None if not cv or len(set(cv)) != 1 else (cv[0] == (0, 0))
        if cz is True:
            succ.append([i + 1] if i + 1 < n else []); continue
        if od == 0 and of == 1:
            succ.append([] if cz is not True else [i + 1]); continue
        if od in ent:  # a call
            succ.append([i + 1] if i + 1 < n else []); continue
        targets = []
        if od in slot:
            tt = table_targets(slot[od])
            if tt and all(t[0] == 'entry' for t in tt):
                succ.append([i + 1] if i + 1 < n else []); continue
            targets = [t[2] for t in tt if t[0] == 'at' and t[1] == f['name']]
        elif od in loc: targets = sorted(loc[od])
        elif re.search(r'Set \{ o: %d, k: EndSentinel' % od, '\n'.join(o for o, _ in code)): succ.append([]); continue
        else: raise ValueError((f['name'], i, op))
        s = [] if cz is True else list(targets)
        if cz is not False and i + 1 < n: s.append(i + 1)
        succ.append(s)
    f['succ'] = succ
def C(f, env, rt, pick=None, stack=(), skip=None):
    """[total, xor, mul, set, deref, jump, keccak] row bounds along f's costliest paths."""
    known = w.known_cells(f, env)
    code = fns[f]['code']; n = len(code)
    extra = {}
    def val(kind, off):
        if off in known: return known[off]
        v = rt(f, kind, off, stack) if rt else None
        if v is None:
            w.UNRES[(f, kind, off)] = w.UNRES.get((f, kind, off), 0) + 1; return 0
        return v
    def sub(g, i, ptr):
        a = w.call_args(f, i, ptr)
        genv = {k: known[s] for k, s in a.items() if s in known}
        return C(g, genv, rt, pick, stack + ((f, i),), skip)
    for i, hs in fns[f]['hints']:
        acc = [0] * 7
        for h in hs:
            if skip and skip(f, h, stack): continue
            if h[0] == 'frame': v = sub(h[2], i, h[1])
            elif h[0] == 'arm':
                ch = pick(f, i, h[3], stack, known.get(h[2])) if pick else None
                if ch is None: ch = range(len(h[3]))
                vs = [sub(h[3][k], i, h[1]) for k in ch]
                v = [max(x[j] for x in vs) for j in range(7)]
            elif h[0] == 'loop':
                _, ptr, g, cnt, bound, tail = h
                k = cnt - 1 if cnt is not None else max(val('loop', bound[0]) - bound[1], 0)
                b = sub(g, i, ptr) if k else [0] * 7
                v = [k * x for x in b]
            else: continue
            acc = [a + b for a, b in zip(acc, v)]
        extra[i] = acc
    succ = fns[f]['succ']
    best = [[0] * 7 for _ in range(n + 1)]
    for i in range(n - 1, -1, -1):
        own = [1] + [0] * 6
        own[1 + w.opk(code[i][0])] = 1
        e = extra.get(i)
        for j in range(7):
            b = max((best[s][j] for s in succ[i] if s > i), default=0)
            best[i][j] = own[j] + (e[j] if e else 0) + b
        if any(s <= i for s in succ[i]): raise ValueError(('back edge', f, i))
    return best[0]
