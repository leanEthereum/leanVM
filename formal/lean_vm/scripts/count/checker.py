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

GT = 2 ** 64          # `gT`: a precondition `(k, a)`, `a >= gT`, reads `a - gT <= b`
GUARDE = 2 ** 20 + 1  # `guardE`: a loop's guard `d = x + y` kept as a tagged bound


def pre_lt(a, e):
    """`preLt`."""
    return a - GT <= e if a >= GT else a < e


def guard_of(b):
    """`guardOf`: a tagged bound `(gT + a, [(k, 0)])`, `(a, k)`."""
    if b[0] >= GT and len(b[1]) == 1 and b[1][0][1] == 0:
        return (b[0] - GT, b[1][0][0])
    return None


def guard_b(rho, c):
    """`guardB`."""
    for (x, b) in rho[1]:
        if x == c: return guard_of(b)
    return None


def guard_atom(cx, rho, s):
    """`guardAtom`."""
    d, x, y = s[2]
    if next((e for (v, e) in cx.ks if v == d), None) != GUARDE: return rho
    a = next((e for (v, e) in rho[0] if v == x), None)
    if a is None: return rho
    return (rho[0], [(d, (GT + a, [(y, 0)]))] + rho[1])


def preB(cx, rho, args, q):
    k, a = q
    if k >= len(args): return None
    c = cx.cls(rho, args[k])
    if c[0] == 'pow': return (0, [], []) if (pre_lt(a, c[1]) and c[1] < ORD) else None
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

def siteBL(cx, rho, g, args, a0, k):
    """`siteBL`: a loop entered on its guard `g^a0 + end`, `None` where it does not apply."""
    c = cx.cert.get(g)
    if c is None or c[0] != 'loop' or c[1] is not None or len(args) < 2: return None
    _, endc, pre, b, ks = c
    if cx.alpha:
        if g not in cx.om: return None
        ph = cx.om[g]
    else: ph = 0
    v0 = cx.cls(rho, args[0])
    if v0 != ('pow', a0) or args[1] != k: return None
    endv = cx.cls(rho, args[1])
    if endv[0] == 'pow':
        e = endv[1]
        if not (a0 <= e and e < ORD): return None
        r = transB(cx, rho, args, pre, b)
        if r is None: return None
        n = e - a0
        return (n * r[0] + ph, [(kk, n * a) for (kk, a) in r[1]], r[2])
    if endv[0] == 'param':
        r = transB(cx, rho, args, pre, b)
        if r is None or r[1] != []: return None
        return (ph, [(endv[1], r[0])], [(endv[1], GT + a0)] + r[2])
    return None


def siteBC(cx, rho, c, g, args):
    """`siteBC`: a `callIf` site, its guard's loop rule where it applies."""
    gd = guard_b(rho, c)
    if gd is not None:
        r = siteBL(cx, rho, g, args, *gd)
        if r is not None: return r
    return siteB(cx, rho, g, args)


TRACK = 2 ** 20

def bnd(cx, rho, v):
    for (x, b) in rho[1]:
        if x == v: return None if guard_of(b) is not None else b
    c = cx.cls(rho, v)
    if c[0] == 'pow': return (c[1], [])
    if c[0] == 'param': return (0, [(c[1], 1)])
    return None

def atomB(cx, rho, s):
    """An atom's bound and the constants and bounds after it (`atomB`), or `None`."""
    if s[1] == 'copy':
        c = cx.cls(rho, s[2][1])
        return acc0(), (([(s[2][0], c[1])] + rho[0], rho[1]) if c[0] == 'pow' else rho)
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
        if b is None: return None
        if c[0] == 'pow':
            if guard_of((b[0] + c[1], b[1])) is not None: return None
            return acc0(), (rho[0], [(d, (b[0] + c[1], b[1]))] + rho[1])
        # `x·y`, `x` a power of `g` where the arguments its bound names are (`powPre`)
        by = bnd(cx, rho, y)
        if by is None: return None
        nb = (b[0] + by[0], b[1] + by[1])
        if guard_of(nb) is not None: return None
        return (0, [], [(k, GT) for (k, _) in b[1]]), (rho[0], [(d, nb)] + rho[1])
    if s[1] == 'add':
        return acc0(), guard_atom(cx, rho, s)
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
        return add(siteBC(cx, rho, s[1], s[2], s[3]), add(ph, blockB(cx, rho, rest)))
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

def call_args(ss):
    """The values a block's calls pass, nested ones included."""
    return {v for s in stmts_all(ss) if s[0] in ('call', 'callIf', 'dispatch') for v in s[2 if s[0] == 'call' else 3]}


def consts(ss):
    """The constant atoms `(d, w)` of a block, nested ones included, in order."""
    return [s[2] for s in walk_atoms(ss) if s[1] == 'const']

def const_args(fns):
    """`(callee, parameter, e)` for each call site passing a value its caller sets to the constant `g^e`, or copies from
    one."""
    out = set()
    for fn in fns.values():
        cw = {}
        for st in walk_atoms(fn['body']):
            if st[1] == 'const' and word_exp(st[2][1]) is not None: cw.setdefault(st[2][0], set()).add(word_exp(st[2][1]))
        for st in walk_atoms(fn['body']):
            if st[1] == 'copy' and st[2][1] in cw: cw.setdefault(st[2][0], set()).update(cw[st[2][1]])
        for st in stmts_all(fn['body']):
            sites = [(st[1], st[2])] if st[0] == 'call' else [(st[2], st[3])] if st[0] == 'callIf' else \
                [(g, st[3]) for g in st[2]] if st[0] == 'dispatch' else []
            for g, args in sites:
                for k, a in enumerate(args):
                    for e in cw.get(a, ()):
                        out.add((g, k, e))
    return out


def stmts_all(ss):
    """The statements of a block, nested ones included, in order."""
    for s in ss:
        yield s
        if s[0] == 'ite':
            yield from stmts_all(s[2]); yield from stmts_all(s[3])
        elif s[0] == 'match':
            for a in s[2]: yield from stmts_all(a)


def walk_atoms(ss):
    """The atoms of a block, nested ones included, in order."""
    return (s for s in stmts_all(ss) if s[0] == 'atom')


def callifs(ss):
    """The `callIf` statements of a block, nested ones included."""
    return [s for s in stmts_all(ss) if s[0] == 'callIf']


def copies(ss):
    """The copy atoms `(d, s)` of a block, nested ones included, in order."""
    return [s[2] for s in walk_atoms(ss) if s[1] == 'copy']


# --- a body at an arm of its first top-level selector (mirror of `Memory.SelArm`) ---
# the functions whose `stat` check is split at their first top-level selector, by name: the selector and its arms
SPLIT = {}


def sel_body(ss, x, r):
    """`selL`: each `match` on `x` its arm `r`'s block inline, each `dispatch` on it its callee `r`'s call."""
    out = []
    for s in ss:
        if s[0] == 'match':
            arms = [sel_body(a, x, r) for a in s[2]]
            if s[1] == x and r < len(arms): out.extend(arms[r])
            else: out.append(('match', s[1], arms))
        elif s[0] == 'ite': out.append(('ite', s[1], sel_body(s[2], x, r), sel_body(s[3], x, r)))
        elif s[0] == 'dispatch' and s[1] == x and r < len(s[2]): out.append(('call', s[2][r], s[3], s[4]))
        else: out.append(s)
    return out


def top_sel(ss):
    """`topSel`: the first top-level `match`'s selector and arms."""
    return next(((s[1], len(s[2])) for s in ss if s[0] == 'match'), None)


def arm_le(ss, x, n):
    """`armLeL`: every `match` and `dispatch` on `x` of at most `n` arms."""
    for s in ss:
        if s[0] == 'match':
            if s[1] == x and len(s[2]) > n: return False
            if not all(arm_le(a, x, n) for a in s[2]): return False
        elif s[0] == 'ite':
            if not (arm_le(s[2], x, n) and arm_le(s[3], x, n)): return False
        elif s[0] == 'dispatch' and s[1] == x and len(s[2]) > n: return False
    return True


def split_blockB(cx, body):
    """`selSplit` of a `stat` check: each arm's bound, their terms equal, the largest constant and every arm's
    preconditions; `None` if an arm fails."""
    sel = top_sel(body)
    if sel is None or not 0 < sel[1] < 2 ** 62 or not arm_le(body, *sel): return None
    rs = [blockB(cx, ([], []), sel_body(body, sel[0], r)) for r in range(sel[1])]
    if any(q is None for q in rs) or any(q[1] != rs[0][1] for q in rs): return None
    return (max(q[0] for q in rs), rs[0][1], [p for q in rs for p in q[2]])


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
    zero = const_args(fns)

    def ks_of(fn):
        used = call_args(fn['body'])
        # the constants a used value copies (`atomB`'s copies)
        for d, src in reversed(copies(fn['body'])):
            if d in used: used.add(src)
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
                if b is not None and b[1] == 'const' and word_exp(b[2][1]) is not None:
                    if not chain(x, acc): return False
                    used.add(y); acc.append(v); return True
                # a product of two bounded values
                if not (chain(x, acc) and chain(y, acc)): return False
                acc.append(v); return True
            for sz in sizes(fn['body'], []):
                acc = []
                if chain(sz, acc):
                    for v in acc:
                        if v not in track: track.append(v)
        # loops' guards `c = x + end` at a `callIf c f (start :: end :: ..)`, `x` a constant (`guardAtom`), and their
        # constants
        guards = []
        cw = {v: w for (v, w) in consts(fn['body'])}
        sums = {}
        for st in walk_atoms(fn['body']):
            if st[1] == 'add': sums.setdefault(st[2][0], st[2])
        for st in callifs(fn['body']):
            sm = sums.get(st[1])
            if sm and len(st[3]) > 1 and sm[2] == st[3][1] and sm[1] in cw and word_exp(cw[sm[1]]) is not None and \
                    sm[2] in fn['params'] and (fn['name'], fn['params'].index(sm[2]), word_exp(cw[sm[1]])) in zero:
                # only where a caller passes the end the start's constant (the run of no iteration)
                if st[1] not in guards: guards.append(st[1])
                used.add(sm[1])
        ks = []
        for (v, w) in consts(fn['body']):
            e = word_exp(w)
            if v in used and e is not None and all(x != v for x, _ in ks): ks.append((v, e))
        return ks + [(v, TRACK) for v in track] + [(v, GUARDE) for v in guards]
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
            if r is None:
                r = split_blockB(cx, fn['body'])
                if r is not None:
                    SPLIT[name] = top_sel(fn['body'])
            if r is not None:
                c = ('stat', dedup(r[2]), (omega[name] + r[0], r[1]), ks)
        if c is not None: cert[name] = c
        state[name] = 'done'
    for i in sorted(fns):
        if only is None or fns[i]['name'] in only: visit(fns[i]['name'])
    return fns, cert


# --- a walk by ranges of statements (mirror of `stmtR`, `stmtRV` and `StaticCut.runS`) ---
def stmt_step(cx, rho, s):
    """A statement's bound and the constants after it (`stmtR`), the latter `None` at a `ret`; `None`
    if it fails."""
    t = s[0]
    if t == 'atom': return atomB(cx, rho, s)
    if t == 'ret': return acc0(), None
    if t == 'ite': r = maxacc(blockB(cx, rho, s[2]), blockB(cx, rho, s[3]))
    elif t == 'match': r = armsB(cx, rho, s[2])
    elif t == 'call': r = siteB(cx, rho, s[1], s[2])
    elif t == 'callIf':
        if s[2] == cx.self: return None
        ph = ((cx.om[s[2]], [], []) if s[2] in cx.om else None) if cx.alpha else acc0()
        r = add(siteBC(cx, rho, s[1], s[2], s[3]), ph)
    elif t == 'dispatch': r = maxB(lambda g: siteB(cx, rho, g, s[3]), s[2])
    else: raise ValueError(t)
    return None if r is None else (r, rho)


def run_range(step, add_, cx, rho, ss):
    """A nonempty range's walk (`runS`): its bounds added and the constants after it, `None` once it
    stops; `None` if a statement fails."""
    acc = None
    for s in ss:
        q = step(cx, rho, s)
        if q is None: return None
        acc = q[0] if acc is None else add_(acc, q[0])
        if q[1] is None: return acc, None
        rho = q[1]
    return acc, rho


# The vector checker (`StaticVec.lean`): a bound's numbers are `Vec`s, read as zero past their end.
def vadd(a, b):
    return [x + y for x, y in zip(a, b)] + a[len(b):] + b[len(a):]

def vmax(a, b):
    return [max(x, y) for x, y in zip(a, b)] + a[len(b):] + b[len(a):]

def vscale(n, a): return [n * x for x in a]

def accv0(): return ([], [], [])

def addv(a, b):
    if a is None or b is None: return None
    return (vadd(a[0], b[0]), a[1] + b[1], a[2] + b[2])

def joinv(a, b):
    if a is None or b is None: return None
    return (vmax(a[0], b[0]), a[1] + b[1], a[2] + b[2])

def certv(cs):
    """The vector certificate of one function's certificates `cs`, a coordinate each, of one shape."""
    c0 = cs[0]
    def aff(bs): return ([b[0] for b in bs], [(q[0], [b[1][t][1] for b in bs]) for t, q in enumerate(bs[0][1])])
    if c0[0] == 'stat': return ('stat', c0[1], aff([c[2] for c in cs]), c0[3])
    return ('loop', c0[1], c0[2], aff([c[3] for c in cs]), c0[4])

def foldv(f, op, l):
    r = accv0()
    for x in reversed([f(y) for y in l]): r = op(x, r)
    return r

def termBV(cx, rho, args, q):
    k, coef = q
    if k >= len(args): return None
    c = cx.cls(rho, args[k])
    if c[0] == 'pow': return (vscale(c[1], coef), [], [])
    if c[0] == 'param': return ([], [(c[1], coef)], [])
    return None

def preBV(cx, rho, args, q):
    k, a = q
    if k >= len(args): return None
    c = cx.cls(rho, args[k])
    if c[0] == 'pow': return accv0() if (pre_lt(a, c[1]) and c[1] < ORD) else None
    if c[0] == 'param': return ([], [], [(c[1], a)])
    return None

def transBV(cx, rho, args, pre, b):
    return addv((b[0], [], []), addv(foldv(lambda q: termBV(cx, rho, args, q), addv, b[1]),
                                    foldv(lambda q: preBV(cx, rho, args, q), addv, pre)))

def siteBV(cx, rho, g, args):
    c = cx.cert.get(g)
    if c is None: return None
    if c[0] == 'stat': return transBV(cx, rho, args, c[1], c[2])
    _, endc, pre, b, ks = c
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
        r = transBV(cx, rho, args, pre, b)
        if r is None: return None
        n = e - a0
        return (vscale(n, r[0]), [(k, vscale(n, v)) for (k, v) in r[1]], r[2])
    if endv[0] == 'param':
        r = transBV(cx, rho, args, pre, b)
        if r is None or r[1] != []: return None
        return ([], [(endv[1], r[0])], [(endv[1], a0)] + r[2])
    return None

def siteBVL(cx, rho, g, args, a0, k):
    """`siteBVL`."""
    c = cx.cert.get(g)
    if c is None or c[0] != 'loop' or c[1] is not None or len(args) < 2: return None
    _, endc, pre, b, ks = c
    if cx.cls(rho, args[0]) != ('pow', a0) or args[1] != k: return None
    endv = cx.cls(rho, args[1])
    if endv[0] == 'pow':
        e = endv[1]
        if not (a0 <= e and e < ORD): return None
        r = transBV(cx, rho, args, pre, b)
        if r is None: return None
        n = e - a0
        return (vscale(n, r[0]), [(kk, vscale(n, v)) for (kk, v) in r[1]], r[2])
    if endv[0] == 'param':
        r = transBV(cx, rho, args, pre, b)
        if r is None or r[1] != []: return None
        return ([], [(endv[1], r[0])], [(endv[1], GT + a0)] + r[2])
    return None


def siteBVC(cx, rho, c, g, args):
    """`siteBVC`."""
    gd = guard_b(rho, c)
    if gd is not None:
        r = siteBVL(cx, rho, g, args, *gd)
        if r is not None: return r
    return siteBV(cx, rho, g, args)


def env_atom(cx, rho, s):
    """The constants after an atom, not counting words (`envAtom`)."""
    if s[1] == 'add':
        return guard_atom(cx, rho, s)
    if s[1] == 'copy':
        e = next((ee for (x, ee) in rho[0] if x == s[2][1]), None)
        return ([(s[2][0], e)] + rho[0], rho[1]) if e is not None else rho
    if s[1] == 'const':
        v, w = s[2]
        e = next((ee for (x, ee) in cx.ks if x == v), None)
        if e is not None and word_exp(w) == e: return ([(v, e)] + rho[0], rho[1])
    return rho

def blockBV(cx, rho, ss):
    if not ss: return accv0()
    q = stmt_stepV(cx, rho, ss[0])
    if q is None: return None
    if q[1] is None: return q[0]
    return addv(q[0], blockBV(cx, q[1], ss[1:]))

def stmt_stepV(cx, rho, s):
    """`stmt_step` of the vector checker (`stmtRV`)."""
    t = s[0]
    if t == 'atom': return accv0(), env_atom(cx, rho, s)
    if t == 'ret': return accv0(), None
    if t == 'ite': r = joinv(blockBV(cx, rho, s[2]), blockBV(cx, rho, s[3]))
    elif t == 'match': r = foldv(lambda a: blockBV(cx, rho, a), joinv, s[2])
    elif t == 'call': r = siteBV(cx, rho, s[1], s[2])
    elif t == 'callIf':
        if s[2] == cx.self: return None
        r = addv(siteBVC(cx, rho, s[1], s[2], s[3]), accv0())
    elif t == 'dispatch': r = foldv(lambda g: siteBV(cx, rho, g, s[3]), joinv, s[2])
    else: raise ValueError(t)
    return None if r is None else (r, rho)

