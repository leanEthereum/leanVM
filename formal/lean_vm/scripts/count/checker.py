"""The static checker of `Memory/Static.lean` (`chkFn`, `blockB`, `siteB`, `atomB`, `loopShape`),
mirrored in Python statement for statement, and the certificates it accepts (`gen`).

Keep it in step with `Memory/Static.lean`: a generated certificate the Lean checker rejects fails
the family's `decide +kernel`, and one it would accept but this mirror misses is lost coverage."""
ORD = 2**64 - 1
POWS = {}


def set_pows(p):
    """The powers of `g` the constants name (`core.load_pows`), for `word_exp`."""
    POWS.clear(); POWS.update(p)


def word_exp(w):
    """The exponent `e` with `constOk w e`: the word is `g^e`, `e < 2^20`."""
    c0, c1 = w
    if c1: return None
    e = POWS.get(c0)
    if e is None and c0 > 0 and c0 & (c0 - 1) == 0 and c0 < 2**64: e = c0.bit_length() - 1
    if e is None or e >= 2**20: return None
    return e

def acc0(): return (0, [], [])
def add(a, b):
    if a is None or b is None: return None
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])

class Ctx:
    def __init__(self, cert, ks, ps, self_, alpha=False, om=None):
        self.cert = cert; self.ks = ks; self.ps = ps; self.self = self_; self.alpha = alpha; self.om = om
    def cls(self, rho, v):
        for (x, e) in rho[0]:
            if x == v: return ('pow', e)
        if v in self.ps: return ('param', self.ps.index(v))
        return ('none',)

def termB(cx, rho, args, q):
    k, coef = q
    if k >= len(args): return None
    c = cx.cls(rho, args[k])
    if c[0] == 'pow': return (coef * c[1], [], [])
    if c[0] == 'param': return (0, [(c[1], coef)], [])
    return None

def preB(cx, rho, args, q):
    k, a = q
    if k >= len(args): return None
    c = cx.cls(rho, args[k])
    if c[0] == 'pow': return (0, [], []) if (a < c[1] and c[1] < ORD) else None
    if c[0] == 'param': return (0, [], [(c[1], a)])
    return None

def maxacc(a, b):
    if a is None or b is None: return None
    return (max(a[0], b[0]), a[1] + b[1], a[2] + b[2])

def maxB(f, l):
    r = acc0()
    for x in reversed([f(y) for y in l]): r = maxacc(x, r)
    return r

def sumB(f, l):
    r = acc0()
    out = []
    for x in l: out.append(f(x))
    # right fold: add(f a, sumB as)
    r = acc0()
    for x in reversed(out): r = add(x, r)
    return r

def transB(cx, rho, args, pre, b):
    return add((b[0], [], []), add(sumB(lambda q: termB(cx, rho, args, q), b[1]),
                                 sumB(lambda q: preB(cx, rho, args, q), pre)))

def siteB(cx, rho, g, args):
    c = cx.cert.get(g)
    if c is None: return None
    if c[0] == 'stat':
        _, pre, b, ks = c
        return transB(cx, rho, args, pre, b)
    _, endc, pre, b, ks = c
    # `phB`: counting words, the run's one phantom frame, charged once
    if cx.alpha:
        if g not in cx.om: return None
        ph = cx.om[g]
    else: ph = 0
    if not args: return None
    v0 = cx.cls(rho, args[0])
    if v0[0] != 'pow': return None
    a0 = v0[1]
    if endc is not None: endv = ('pow', endc)
    elif len(args) > 1: endv = cx.cls(rho, args[1])
    else: endv = ('none',)
    if endv[0] == 'pow':
        e = endv[1]
        if not (a0 < e and e < ORD): return None
        r = transB(cx, rho, args, pre, b)
        if r is None: return None
        n = e - a0
        return (n * r[0] + ph, [(k, n * a) for (k, a) in r[1]], r[2])
    if endv[0] == 'param':
        k = endv[1]
        r = transB(cx, rho, args, pre, b)
        if r is None or r[1] != []: return None
        return (ph, [(k, r[0])], [(k, a0)] + r[2])
    return None

TRACK = 2 ** 20

def bnd(cx, rho, v):
    for (x, b) in rho[1]:
        if x == v: return b
    c = cx.cls(rho, v)
    if c[0] == 'pow': return (c[1], [])
    if c[0] == 'param': return (0, [(c[1], 1)])
    return None

def atomB(cx, rho, s):
    """An atom's bound and the constants and bounds after it (`atomB`), or `None`."""
    if s[1] == 'const':
        v, w = s[2]
        e = next((ee for (x, ee) in cx.ks if x == v), None)
        if e is not None and word_exp(w) == e:
            return acc0(), ([(v, e)] + rho[0], rho[1])
        return acc0(), rho
    if cx.alpha and s[1] == 'alloc':
        return (s[2], [], []), rho
    if cx.alpha and s[1] == 'allocDyn':
        b = bnd(cx, rho, s[2])
        if b is None: return None
        return (b[0], b[1], []), rho
    if cx.alpha and s[1] == 'mul' and next((ee for (x, ee) in cx.ks if x == s[2][0]), None) == TRACK:
        d, x, y = s[2]
        b = bnd(cx, rho, x); c = cx.cls(rho, y)
        if b is None or c[0] != 'pow': return None
        return acc0(), (rho[0], [(d, (b[0] + c[1], b[1]))] + rho[1])
    return acc0(), rho


def block_env(cx, rho, ss):
    """The constants and bounds after a block's top-level atoms (`blockEnv`)."""
    for s in ss:
        if s[0] == 'atom':
            r = atomB(cx, rho, s)
            if r is None: return rho
            rho = r[1]
    return rho


def blockB(cx, rho, ss):
    if not ss: return acc0()
    s, rest = ss[0], ss[1:]
    t = s[0]
    if t == 'atom':
        r = atomB(cx, rho, s)
        if r is None: return None
        return add(r[0], blockB(cx, r[1], rest))
    if t == 'ite':
        return add(maxacc(blockB(cx, rho, s[2]), blockB(cx, rho, s[3])), blockB(cx, rho, rest))
    if t == 'match':
        return add(armsB(cx, rho, s[2]), blockB(cx, rho, rest))
    if t == 'call':
        return add(siteB(cx, rho, s[1], s[2]), blockB(cx, rho, rest))
    if t == 'callIf':
        if s[2] == cx.self: return None
        ph = ((cx.om[s[2]], [], []) if s[2] in cx.om else None) if cx.alpha else acc0()
        return add(siteB(cx, rho, s[2], s[3]), add(ph, blockB(cx, rho, rest)))
    if t == 'dispatch':
        return add(maxB(lambda g: siteB(cx, rho, g, s[3]), s[2]), blockB(cx, rho, rest))
    if t == 'ret':
        return acc0()
    raise ValueError(t)

def armsB(cx, rho, arms):
    r = acc0()
    for a in reversed(arms): r = maxacc(blockB(cx, rho, a), r)
    return r

# --- loop shape (mirror of loopShape) ---
def no_ret(ss):
    for s in ss:
        if s[0] == 'ret': return False
        if s[0] == 'ite' and not (no_ret(s[2]) and no_ret(s[3])): return False
        if s[0] == 'match' and not all(no_ret(a) for a in s[2]): return False
    return True

def defAtom(d, pre):
    for s in pre:
        if s[0] == 'atom' and s[1] in ('const', 'add', 'mul') and s[2][0] == d:
            return s
    return None

def loop_shape(fn, endc):
    body = fn['body']; ps = fn['params']
    if len(body) < 2 or body[-1] != ('ret', []) or body[-2][0] != 'callIf' or not ps: return None
    _, c, g, targs = body[-2]
    if g != fn['name'] or not targs or targs[1:] != ps[1:]: return None
    pre = body[:-2]
    if not no_ret(pre): return None
    p0 = ps[0]; p1 = ps[1] if len(ps) > 1 else None
    def isG(z):
        a = defAtom(z, pre); return a is not None and a[1] == 'const' and word_exp(a[2][1]) == 1
    def isStep(p, d):
        a = defAtom(d, pre)
        if a is None or a[1] != 'mul': return False
        _, x, y = a[2]
        return (x == p and isG(y)) or (y == p and isG(x))
    def isEnd(y):
        if endc is None: return p1 == y
        a = defAtom(y, pre); return a is not None and a[1] == 'const' and word_exp(a[2][1]) == endc
    if not isStep(p0, targs[0]): return None
    a = defAtom(c, pre)
    if a is None or a[1] != 'add': return None
    _, x, y = a[2]
    if (isStep(p0, x) and isEnd(y)) or (isStep(p0, y) and isEnd(x)): return pre
    return None

def const_end(fn):
    """The constant end of a helper whose guard compares with a constant, if any."""
    body = fn['body']; ps = fn['params']
    if len(body) < 2 or body[-2][0] != 'callIf': return None
    pre = body[:-2]; c = body[-2][1]
    a = defAtom(c, pre)
    if a is None or a[1] != 'add': return None
    for y in a[2][1:]:
        b = defAtom(y, pre)
        if b is not None and b[1] == 'const':
            e = word_exp(b[2][1])
            if e is not None: return e
    return None

def call_args(ss, out):
    for s in ss:
        if s[0] == 'call': out.update(s[2])
        elif s[0] == 'callIf': out.update(s[3])
        elif s[0] == 'dispatch': out.update(s[3])
        elif s[0] == 'ite': call_args(s[2], out); call_args(s[3], out)
        elif s[0] == 'match':
            for a in s[2]: call_args(a, out)
    return out

def consts(ss, out):
    for s in ss:
        if s[0] == 'atom' and s[1] == 'const': out.append(s[2])
        elif s[0] == 'ite': consts(s[2], out); consts(s[3], out)
        elif s[0] == 'match':
            for a in s[2]: consts(a, out)
    return out

def callees(ss, out):
    for s in ss:
        if s[0] == 'call': out.add(s[1])
        elif s[0] == 'callIf': out.add(s[2])
        elif s[0] == 'dispatch': out.update(s[2])
        elif s[0] == 'ite': callees(s[2], out); callees(s[3], out)
        elif s[0] == 'match':
            for a in s[2]: callees(a, out)
    return out

def dedup(l):
    out = []
    for x in l:
        if x not in out: out.append(x)
    return out

def gen(fns, omega, alpha=False, hand=None, only=None):
    """The certificates the checker accepts at frame weights `omega` (by name), counting words if
    `alpha`: each function's after its callees', a loop helper's per iteration; `hand` gives
    certificates taken as given (`HandOk`), `only` restricts to a set of names (closed under calls)."""
    hand = hand or {}
    byname = {f['name']: i for i, f in fns.items()}
    cert = {}
    state = {}
    def ks_of(fn):
        used = call_args(fn['body'], set())
        track = []
        if alpha:
            defs = {}
            def scan(ss):
                for s in ss:
                    if s[0] == 'atom' and s[1] in ('const', 'add', 'mul'): defs.setdefault(s[2][0], s)
                    elif s[0] == 'ite': scan(s[2]); scan(s[3])
                    elif s[0] == 'match':
                        for a in s[2]: scan(a)
            scan(fn['body'])
            def sizes(ss, out):
                for s in ss:
                    if s[0] == 'atom' and s[1] == 'allocDyn': out.append(s[2])
                    elif s[0] == 'ite': sizes(s[2], out); sizes(s[3], out)
                    elif s[0] == 'match':
                        for a in s[2]: sizes(a, out)
                return out
            def chain(v, acc):
                # v bounded: a parameter, a constant g^e, or x * g^c with x bounded
                if v in fn['params']: return True
                a = defs.get(v)
                if a is None: return False
                if a[1] == 'const': return word_exp(a[2][1]) is not None and (used.add(v) or True)
                if a[1] != 'mul': return False
                _, x, y = a[2]
                b = defs.get(y)
                if b is None or b[1] != 'const' or word_exp(b[2][1]) is None: return False
                if not chain(x, acc): return False
                used.add(y); acc.append(v); return True
            for sz in sizes(fn['body'], []):
                acc = []
                if chain(sz, acc):
                    for v in acc:
                        if v not in track: track.append(v)
        ks = []
        for (v, w) in consts(fn['body'], []):
            e = word_exp(w)
            if v in used and e is not None and all(x != v for x, _ in ks): ks.append((v, e))
        return ks + [(v, TRACK) for v in track]
    def visit(name):
        if name in state: return
        if name in hand:
            cert[name] = hand[name]; state[name] = 'done'; return
        state[name] = 'busy'
        fn = fns[byname[name]]
        for g in callees(fn['body'], set()):
            if g != name: visit(g)
        ks = ks_of(fn)
        cx = Ctx(cert, ks, fn['params'], name, alpha, omega)
        c = None
        if name.startswith('__loop'):
            for endc in (None, const_end(fn)):
                pre = loop_shape(fn, endc)
                if pre is None: continue
                r = blockB(cx, ([], []), pre)
                if r is None: continue
                b = (omega[name] + r[0], r[1]); pr = dedup(r[2])
                if all(k != 0 for k, _ in b[1]) and all(k != 0 for k, _ in pr):
                    c = ('loop', endc, pr, b, ks)
                break
        else:
            r = blockB(cx, ([], []), fn['body'])
            if r is not None:
                c = ('stat', dedup(r[2]), (omega[name] + r[0], r[1]), ks)
        if c is not None: cert[name] = c
        state[name] = 'done'
    for i in sorted(fns):
        if only is None or fns[i]['name'] in only: visit(fns[i]['name'])
    return fns, cert

