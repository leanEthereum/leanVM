"""The guest's compiled code, read from the generated data (no inference): each compiled function's code, hints,
arguments and returned words (`Pack/*/{Bundle,Sig}.lean`), the advice's hints (`data.advice`), the powers of `g`, the
jump table; from them (`derive`) each function's operations, table jumps, callees, loop helpers and frame signature
(its entry and return cells by the frame layout, a loop's self cell); and the Lean literals the core route's
generators print."""
import re, glob, os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_VM = os.path.normpath(os.path.join(HERE, '..', '..'))
ROOT = os.path.join(LEAN_VM, 'LeanVM', 'Guest')
STATEMENT = os.path.normpath(os.path.join(LEAN_VM, '..', 'Statement'))
# the bridge's readers (`scripts/bridge-cert/`: `data`, the packs' one reader, and `align`) after this directory's
# modules, whose `pair.py` is not the bridge's
BRIDGE = os.path.join(os.path.dirname(HERE), 'bridge-cert')
if BRIDGE not in sys.path:
    sys.path.append(BRIDGE)
import data as BD  # noqa: E402


def load():
    ins_re=re.compile(r'\(\.(\w+) ([^()]*)\)')
    fns={}
    for name, (pack, blk) in BD.bundle_blocks().items():
        chunks={}
        for m in re.finditer(r'def (c\d+) : List OffsetInstruction := \[(.*?)\]\n', blk, re.S):
            body=m.group(2)
            L=[]
            for im in ins_re.finditer(body):
                op=im.group(1); args=im.group(2).split()
                L.append((op,args))
            chunks[m.group(1)]=L
        nm,entry,cnt,cl=BD.code_of(blk)
        code=[]
        for c in cl:
            code+=chunks[c]
        assert len(code)==cnt,(nm,len(code),cnt)
        fns[nm]=dict(name=nm,entry=entry,count=cnt,code=code,pack=pack,ns=name)
    for b in sorted(glob.glob(ROOT+'/Pack/*/Sig.lean')):
        s=open(b).read()
        for m in re.finditer(r'def sig : Check.Sig :=\s*⟨"([^"]*)", (\d+|Fn\.«[^»]+»\.entry), (\d+), (\d+),',s):
            fns[m.group(1)]['nargs']=int(m.group(3)); fns[m.group(1)]['nret']=int(m.group(4))
    # the hints by pc, as the bridge reads them (`data.isa_hint`)
    hints = {pc: hs for A in BD.advice().values() for pc, hs in A['hints']}
    g = open(os.path.join(ROOT, 'Data', 'Pows.lean')).read()
    pows = {int(k): int(e) for k, e in re.findall(r'\.node (\d+) (\d+)', g)}
    t = open(os.path.join(STATEMENT, 'Data', 'Bytecode00.lean')).read()
    blk = t[t.index('def f0c0'):]
    t0 = open(os.path.join(STATEMENT, 'Data', 'Bytecode.lean')).read()
    n0 = int(re.search(r'def f0 : CompiledFunction :=\s*⟨"[^"]*", \d+, (\d+)', t0).group(1))
    f0 = [(int(a), int(b)) for a, b, _ in re.findall(r'\.set (\d+) (\d+) (\d+)', blk)][:n0]
    jt = {s: pows.get(k) for s, k in f0}
    return dict(fns=fns, hints=hints, pows=pows, jt=jt)


def _jt_lo():
    """The jump table's first cell: `main`'s frame size (`Data/FrameSizes.lean`'s `mainCells`)."""
    t = open(os.path.join(ROOT, 'Data', 'FrameSizes.lean')).read()
    return int(re.search(r'abbrev mainCells : ℕ := (\d+)', t).group(1))


JT_LO, HALT = _jt_lo(), BD.HALT


def conv(op, a):
    if op in ('xor', 'mul', 'set', 'jump'): return tuple(map(int, a))
    if op == 'deref': return (int(a[0]), int(a[1]), int(a[2]), a[3])
    if op == 'keccak': return tuple(map(int, a[:8])) + (a[8] == 'true', a[9] == 'true', a[10])
    raise Exception(op)


def table_jump(c, i):
    """Operation `i` a table call's `JUMP` through the cell the `DEREF` before it loaded."""
    a, b = c[i - 1], c[i]
    return a[0] == 'deref' and b[0] == 'jump' and a[1][3] == '.cell' and a[1][2] == b[1][1]


def derive(P):
    """The code's operations (`ops`), hints by offset (`hints`), table jumps with their regions' sizes (`tabs`),
    callees (`calls`), loop helpers (`isloop`), and each function's frame signature `(entry, self, ret)` (`fsig`,
    by entry pc): its header and argument cells, a loop's self cell (the cell its code sets to its own frame), its
    returned words' cells."""
    fns, HINTS, POWS, JT = P['fns'], P['hints'], P['pows'], P['jt']
    byentry = {f['entry']: f for f in fns.values()}
    JT_HI = max(JT) + 1
    assert sorted(JT) == list(range(JT_LO, JT_HI))
    for f in fns.values():
        f['ops'] = [(op, conv(op, a)) for op, a in f['code']]
        f['hints'] = {pc - f['entry']: hs for pc, hs in HINTS.items() if f['entry'] <= pc < f['entry'] + f['count']}
    bl = sorted({f['ops'][i - 1][1][1] for f in fns.values() for i in range(1, len(f['ops'])) if table_jump(f['ops'], i)})
    region = {t: (bl[k + 1] if k + 1 < len(bl) else JT_HI) - t for k, t in enumerate(bl)}
    calls = collections.defaultdict(set)
    for f in fns.values():
        c = f['ops']
        f['tabs'] = {i: region[c[i - 1][1][1]] for i in range(1, len(c)) if table_jump(c, i)}
        # a call: an entry pc set in a cell one of the function's `JUMP`s targets (not a table's constant equal to one)
        targets = {a[1] for op, a in c if op == 'jump'}
        for op, a in c:
            if op == 'set' and a[2] == 0 and POWS.get(a[1]) in byentry and a[0] in targets:
                calls[f['name']].add(byentry[POWS[a[1]]]['name'])
        for i, r in f['tabs'].items():
            for j in range(r):
                g = byentry.get(JT.get(c[i - 1][1][1] + j))
                if g: calls[f['name']].add(g['name'])
    isloop = {n for n in fns if n in calls[n]}
    # a loop's self cell: the cell a `DEREF` stores its own frame through, before the `JUMP` to its own entry
    selfc = {}
    for f in fns.values():
        c = f['ops']
        for i, (op, a) in enumerate(c):
            if op == 'deref' and a[3] == '.cell' and a[0] == a[2]:
                for d in range(1, 5):
                    if i + d < len(c) and c[i + d][0] == 'jump':
                        od = c[i + d][1][1]
                        for k in range(i - 1, max(-1, i - 300), -1):
                            if c[k][0] == 'set' and c[k][1][0] == od:
                                e = POWS.get(c[k][1][1])
                                if e is not None: selfc[e] = a[1]
                                break
                        break
    fsig = {}
    for n, f in fns.items():
        na, nr = f['nargs'], f['nret']
        fsig[f['entry']] = ([0, 1] + list(range(2, 2 + na)), selfc.get(f['entry']) if n in isloop else None,
                            list(range(2 + na, 2 + na + nr)))
    return dict(P, calls=calls, isloop=isloop, fsig=fsig, jt_lo=JT_LO, jt_hi=JT_HI, halt=HALT)


_CODE = []


def code():
    """`derive(load())`, once."""
    if not _CODE:
        _CODE.append(derive(load()))
    return _CODE[0]


# ---- Lean literals, and printed ones read back

def tokens(s):
    return re.findall(r'⟨|⟩|\[|\]|\(|\)|,|[A-Za-z_.][A-Za-z_.0-9]*|\d+', s)


def parse(s):
    """A printed Lean term of `Mode.Sig`'s parts as Python: anonymous constructors as tuples, lists as
    lists, `.c a b` as `('c', a, b)`, `List.flatten l` flattened."""
    ts = tokens(s); pos = [0]

    def term():
        t = ts[pos[0]]
        if t == '⟨':
            pos[0] += 1; out = []
            while ts[pos[0]] != '⟩':
                out.append(app())
                if ts[pos[0]] == ',': pos[0] += 1
            pos[0] += 1
            return tuple(out)
        if t == '[':
            pos[0] += 1; out = []
            while ts[pos[0]] != ']':
                out.append(app())
                if ts[pos[0]] == ',': pos[0] += 1
            pos[0] += 1
            return out
        if t == '(':
            pos[0] += 1; vs = [app()]
            while ts[pos[0]] == ',':
                pos[0] += 1; vs.append(app())
            assert ts[pos[0]] == ')', (s, pos[0]); pos[0] += 1
            return vs[0] if len(vs) == 1 else tuple(vs)
        pos[0] += 1
        if t.isdigit(): return int(t)
        return ('id', t)

    def app():
        head = term()
        args = []
        while pos[0] < len(ts) and ts[pos[0]] not in (',', ')', ']', '⟩'):
            args.append(term())
        if not args: return head
        h = head[1]
        if h == 'List.flatten': return [x for l in args[0] for x in l]
        return (h.lstrip('.'),) + tuple(args)

    return app()


def split_top(s):
    out = []; depth = 0; cur = ''
    for ch in s:
        if ch in '⟨([{': depth += 1
        if ch in '⟩)]}': depth -= 1
        if ch == ',' and depth == 0: out.append(cur.strip()); cur = ''
        else: cur += ch
    out.append(cur.strip())
    return out


LONG = 16


def nat(n): return str(n)


def base(b): return '(.fr %d)' % b[1] if b[0] == 'fr' else '(.hp %d %d)' % (b[1], b[2])


def mono(m): return '⟨%d, %d, [%s]⟩' % (m[0], m[1], ', '.join('(%s, %d)' % (base(b), e) for b, e in m[2]))


def idx(i): return '(.num %d)' % i[1] if i[0] == 'num' else '(.ex %s %d)' % (base(i[1]), i[2])


def rng(r): return '⟨%s, %s, %s, %d, %d⟩' % (mono(r[0]), idx(r[1]), idx(r[2]), r[3], r[4])


def lst(xs, f=nat):
    """A list literal, a long one as `List.flatten` of lists of at most `LONG`, nested."""
    xs = list(xs)
    if len(xs) <= LONG: return '[%s]' % ', '.join(f(x) for x in xs)
    parts = [xs[i:i + LONG] for i in range(0, len(xs), LONG)]

    def tree(ps):
        if len(ps) == 1: return '[%s]' % ', '.join(f(x) for x in ps[0])
        step = LONG
        while len(ps) > step * LONG: step *= LONG
        groups = [ps[i:i + step] for i in range(0, len(ps), step)] if len(ps) > LONG else [[p] for p in ps]
        return '(List.flatten [%s])' % ', '.join(tree(g) for g in groups)
    return tree(parts)


def res(r):
    """A residual (`Mode.Res`)."""
    if r[0] == 'lt': return '(.lt %s %s)' % (idx(r[1]), idx(r[2]))
    if r[0] == 'sub': return '(.sub %s %s)' % (rng(r[1]), lst(r[2], rng))
    if r[0] == 'name': return '(.name %d)' % r[1]
    return '(.nz %d)' % r[1]


def trie(entries, val):
    """A literal `Exec.Trie`: key `0` at the root, `2m+1` at key `m` of the left child, `2m+2` at the
    right one's."""
    return bigTrie(None, None, entries, val, None)


# a literal trie's subtree longer than this is a definition of its own (`bigTrie`)
BIG = 40000


def bigTrie(name, typ, entries, val, defs):
    """`trie`, each subtree longer than `BIG` a definition `{name}{k}` of its own, written to `defs` (none if `defs` is
    None)."""
    def build(es):
        if not es: return '.nil'
        here = None; left = []; right = []
        for k, v in es:
            if k == 0: here = v
            elif k % 2 == 1: left.append((k // 2, v))
            else: right.append((k // 2 - 1, v))
        t = '(.node %s %s %s)' % ('none' if here is None else '(some %s)' % val(here), build(left), build(right))
        if defs is not None and len(t) > BIG:
            d = '%s%d' % (name, len(defs))
            defs.append('noncomputable def %s : Exec.Trie (%s) :=\n  %s\n\n' % (d, typ, t))
            return d
        return t
    return build(sorted(entries.items()))


def wrap(text, width=100):
    """Long lines broken at spaces (no generated string literal holds one), the rest indented: Lean's
    positions are slow to compute on very long lines. Linear in the line's length."""
    out = []
    for line in text.split('\n'):
        p, pre = 0, ''
        while len(pre) + len(line) - p > width:
            d = p - len(pre)  # the piece's column 0 in the line
            k = line.rfind(' ', p, d + width)
            if k < 0 or k - d <= 4: k = line.find(' ', d + width)
            if k < 0: break
            out.append(pre + line[p:k]); p, pre = k + 1, '    '
        out.append(pre + line[p:])
    return '\n'.join(out)


def fnq(n): return 'Fn.«%s»' % code()['fns'][n]['ns']


def packs():
    """Each pack's functions (compiled names), by entry."""
    by = collections.defaultdict(list)
    for n, f in code()['fns'].items(): by[f['pack']].append(n)
    return {p: sorted(ns, key=lambda n: code()['fns'][n]['entry']) for p, ns in by.items()}


def calleesOf(n): return sorted(code()['calls'][n])
