"""The heap certificates of `infer.py` in `heapOkC`'s input format (`m2-format.md`, `CoreMode/Defs.lean`), and their
checks.

The inference gives each function's signature and residuals; the witnesses are then found in `heapOkC`'s own pass
(`heapc.py`, the check in Python step for step): each read, callee precondition and own guarantee gets a witness of
the check's scope (an event's serial, a precondition, a run or pointer fact or pointer run in scope with the residuals
it needs, `pts`, `cat`, `mrg`, `word`, `skip`), so serials, joins and selector guarantees are the check's. The reads
taking a stored word (`hvs`), the quotients (`divs`) and the callees' ghost words (`gargs`) follow the inference's
values. What the check cannot witness is reported by cause; only functions the Python check passes get a kernel check.

Per pack: `LeanVM/Guest/CoreMode/GenC/<pack>/Data.lean`, every function's `hcert`; `Ok.lean`,
`heap_okC : heapOkC Data.powTree sigOf core hcert = true` for each function whose certificate passes, `sigOf` its
callees' signatures by their `Fn.name`.

usage (from formal/lean_vm): python3 -I scripts/core-mode/emitc.py [--with F,..] [--without F,..] [--out DIR] [--check]
  [--mods FILE] [--fn NAME] [--report FILE]
"""
import sys, os, collections, glob, re, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
argv = list(sys.argv)
sys.argv = sys.argv[:1]
import infer as I
import heapc as C

GUEST = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
NAME = {k: nm for nm, k in I.STABLE.items()}
# the inference's features `heapOkC` has no counterpart of, off by default: offsets modulo `g`'s order (cells are
# naturals there), range checks as free facts (there every fact is a residual), a dispatch's returned pointers and a
# run with its point before it (`retP`: no witness form places `Q·h^S` in `⟨Q·g^S, S, 0, h⟩`)
OFF = {'wrap', 'lts', 'retP'}
PTSMAX = 4096
# functions whose kernel check runs past the build's memory cap (`lake-build.py --cap 36`): their certificate is
# emitted, their `heap_okC` not (one `decide` over the whole body; a windowed check is a request to the heap side)
KERNEL_SKIP = {'main_loop2'}


# ---- the inference's values, recorded as it assigns them

def _instrument():
    atom0, call0 = I.Pass.atom, I.Pass.call

    def atom(self, st, a):
        atom0(self, st, a)
        rec = self.__dict__.setdefault('envrec', {})
        k = a[0]
        vs = a[1:4] if k in ('load', 'mul', 'copy', 'assertEq', 'add') else a[1:2]
        for v in vs:
            if isinstance(v, int) and v in st.env and v not in rec:
                rec[v] = st.env[v]

    def call(self, st, f, args, rets, *a, **kw):
        call0(self, st, f, args, rets, *a, **kw)
        rec = self.__dict__.setdefault('envrec', {})
        for v in rets or ():
            if v in st.env and v not in rec:
                rec[v] = st.env[v]
    pushR0 = I.Pass.pushR

    def pushR(self, st, r):
        self.__dict__.setdefault('runlog', []).append((self.nr, r))
        pushR0(self, st, r)
    I.Pass.atom, I.Pass.call, I.Pass.pushR = atom, call, pushR


_instrument()


class Unsupported(Exception):
    pass


# ---- translation of the inference's data

def cell(c, m=None):
    """An inference monomial as a `CCell`; ghost bases `GB + j` of a signature to slot `m + j` when `m` is given."""
    if c[1] < 0 or c[1] >= C.CAPE or any(e <= 0 for _, e in c[0]):
        raise Unsupported(('cell', c))
    if m is None:
        return (tuple(c[0]), c[1])
    bs = C.mergeB(tuple((m + b - I.GB if b >= I.GB else b, e) for b, e in c[0]), ())
    return (bs, c[1])


def cidx(c, m=None):
    c = cell(c, m)
    if not c[0]:
        return ('num', c[1])
    if len(c[0]) == 1 and c[0][0][1] == 1 and c[1] == 0:
        return ('val', c[0][0][0])
    return ('mono', c)


def crun(r, m=None):
    Q, S, lo, hi = r
    return (cell(Q, m), S, cidx(lo, m), cidx(hi, m))


def sig_of(G, m, drops):
    """The inference's signature as an `HSig`; entries it cannot state dropped (listed in `drops`)."""
    def each(name, xs, f):
        out = []
        for x in xs:
            try:
                out.append(f(x))
            except Unsupported as e:
                drops.append((name, e.args[0]))
        return out
    H = C.HSig()
    H.pre = each('pre', G.pre, lambda c: cell(c, m))
    H.post = each('post', G.post, lambda c: cell(c, m))
    H.preR = each('preR', G.preR, lambda r: crun(r, m))
    H.postR = each('postR', G.postR, lambda r: crun(r, m))
    H.term = each('term', G.term, lambda t: (cidx(t[0], m), cidx(t[1], m)))
    H.retM = each('retM', sorted(G.retM.items()), lambda p: (p[0], cell(p[1], m)))
    H.preP = each('preP', G.preP, lambda p: (cell(p[0], m), tuple(sorted(p[1]))))
    H.postP = each('postP', G.postP, lambda p: (cell(p[0], m), tuple(sorted(p[1]))))
    H.prePR = each('prePR', G.prePR, lambda p: (crun(p[0], m), tuple(sorted(p[1]))))
    H.postPR = each('postPR', G.postPR, lambda p: (crun(p[0], m), tuple(sorted(p[1]))))

    def pv(p):
        c = cell(p[0], m)
        if c not in H.post:
            raise Unsupported(('postV-cell', p[0]))
        return (H.post.index(c), cell(p[1], m))
    H.postV = each('postV', G.postV, pv)
    H.ghosts = len(G.ghosts)
    return H


def res_of(r):
    """An inference residual as a `CRes` over value numbers (`None`: a derived run's, which the check states by its
    witness forms instead)."""
    k = r[0]
    if k == 'lt':
        if len(r) > 4 and r[4] is not None:
            (ka, a), (kb, b) = r[4]
            return ('lt', (ka, a), (kb, b))
        return ('lt', cidx(r[1]), cidx(r[2]))
    if k == 'sub' and len(r) > 3 and r[3] == 'narrow':
        return ('sub', cell(r[1]), crun(r[2]))
    if k == 'sub' and len(r[2]) == 1 and len(r) == 3:
        return ('subR', crun(r[1]), crun(r[2][0]))
    if k == 'subR':
        q = r[1]
        if len(q) == 3:
            q = ((q[0], q[1]), 1, I.num(0), I.num(q[2] - q[1]))
        return ('subR', crun(q), crun(r[2]))
    return None


def conds_of(paths):
    """The branch conditions common to the paths a residual was asked on (`CRes.under`)."""
    cs = None
    for p in paths:
        c = [('zero', x[1]) if x[0] == 'ite' and x[2] else ('nonzero', x[1]) if x[0] == 'ite' else ('arm', x[1], x[2])
             for x in p]
        cs = c if cs is None else [x for x in cs if x in c]
    return tuple(dict.fromkeys(cs or ()))


# ---- the solver: each witness found in the check's scope

class Solver:
    def __init__(self, k, P, H, sigs):
        self.k, self.P, self.H = k, P, H
        self.sigs = sigs
        self.lean_res = {}         # inference residual index -> the certificate's
        self.pool_lt, self.pool_sub = [], []
        self.drops = []
        for i in sorted(I.used_res(P)):
            try:
                r = res_of(P.res[i])
            except Unsupported as e:
                self.drops.append(('res', e.args[0]))
                continue
            if r is None:
                continue
            g = conds_of(P.rpath.get(i, ()))
            wr = ('under', g, r) if g else r
            (self.pool_lt if r[0] == 'lt' else self.pool_sub).append((i, r, wr))
        self.sites = collections.defaultdict(list)
        for f, args, gi, _ in P.sites:
            self.sites[(f, tuple(args))].append(gi)
        self.envrec = P.__dict__.get('envrec', {})
        self.stats = collections.Counter()

    # -- residuals and facts
    def on(self, pool):
        """The residuals usable on the site's path."""
        return [e for e in pool if C.unU(self.X.path, e[2]) is not None]

    def use(self, i, r):
        j = self.lean_res.get(i)
        if j is None:
            j = self.lean_res[i] = len(self.H.res)
            self.H.res.append(r)
        return j

    def fact(self, st, a, b):
        """Residuals giving the fact `(a, b)`: `[]` from the own term, `None` if none."""
        X = self.X
        for p in X.facts(st.env, []):
            if p == (a, b):
                return []
        for i, r, wr in self.on(self.pool_lt):
            if C.idxF(st.env, r[1]) == a and C.idxF(st.env, r[2]) == b:
                return [self.use(i, wr)]
        return None

    def factC(self, st, k, b):
        """A fact `(g^k', b)`, `k <= k' < 2^62`."""
        X = self.X
        for p in X.facts(st.env, []):
            if not p[0][0] and k <= p[0][1] < C.CAPE and p[1] == b:
                return []
        for i, r, wr in self.on(self.pool_lt):
            a = C.idxF(st.env, r[1])
            if not a[0] and k <= a[1] < C.CAPE and C.idxF(st.env, r[2]) == b:
                return [self.use(i, wr)]
        return None

    def factU(self, st, a, j):
        """A fact `(a, g^h)`, `h <= j`."""
        for p in self.X.facts(st.env, []):
            if p[0] == a and not p[1][0] and p[1][1] <= j:
                return []
        for i, r, wr in self.on(self.pool_lt):
            b = C.idxF(st.env, r[2])
            if not b[0] and b[1] <= j and C.idxF(st.env, r[1]) == a:
                return [self.use(i, wr)]
        return None

    def factE(self, st, m):
        """`m` has an exponent: a constant, or a side of a fact."""
        if not m[0] and m[1] < C.CAPE:
            return []
        for p in self.X.facts(st.env, []):
            if m in p:
                return []
        for i, r, wr in self.on(self.pool_lt):
            if C.idxF(st.env, r[1]) == m or C.idxF(st.env, r[2]) == m:
                return [self.use(i, wr)]
        # none: the inference's `merge` takes the root's exponent for granted; stated as a residual of its own
        # (`exp`: the word is `g^y`, `y < 2^62 - 1`)
        r = ('lt', ('val', m[0][0][0]) if m[1] == 0 and len(m[0]) == 1 and m[0][0][1] == 1 else ('mono', m),
             ('num', C.CAPE - 1))
        self.stats['exp-res'] += 1
        return [self.use(('exp', m), r)]

    # -- a cell of a run (`ptRun`), the residuals it needs
    def in_run(self, st, R, c):
        base, S, lo, hi = R
        if c == C.cmul(base, C.cpow(lo, S)):
            f = self.fact(st, lo, hi)
            if f is not None:
                return f
        J = C.idxOf(base, c, S)
        if c == C.cmul(base, C.cpow(J, S)):
            f = self.fact(st, J, hi)
            if f is not None:
                if lo == ((), 0) or lo == J:
                    return f
                f2 = self.fact(st, lo, C.cshift(J, 1))
                if f2 is not None:
                    return sorted(set(f + f2))
        if c[0] == base[0] and base[1] <= c[1] and S and (c[1] - base[1]) % S == 0 and not lo[0] and lo[1] < C.CAPE:
            k = (c[1] - base[1]) // S
            if lo[1] <= k:
                if not hi[0] and hi[1] < C.CAPE and k < hi[1]:
                    return []
                f = self.factC(st, k, hi)
                if f is not None:
                    return f
        return None

    def run_in(self, st, Q, R):
        """`runRun`: the run `Q` inside `R`, the residuals it needs."""
        if Q[0] != R[0] or Q[1] != R[1]:
            return None
        res = []
        if not (Q[2] == R[2] or (not Q[2][0] and not R[2][0] and R[2][1] <= Q[2][1] < C.CAPE)):
            if Q[2] != C.cshift(R[2], 1):
                return None
            f = self.fact(st, R[2], R[3])
            if f is None:
                return None
            res += f
        if not (Q[3] == R[3] or (not Q[3][0] and not R[3][0] and Q[3][1] <= R[3][1] < C.CAPE)):
            if Q[3][0] or Q[3][1] >= C.CAPE:
                return None
            f = self.factC(st, C.tsub(Q[3][1], 1), R[3])
            if f is None:
                return None
            res += f
        return sorted(set(res))

    # -- witnesses
    def pt(self, st, c, want=None, depth=0):
        """A witness of the cell `c` (`ptOk`); with `want`, a load event that stored that word."""
        sers = st.c2s.get(c, ())
        if want is not None:
            for n in sers:
                q = st.sv.get(n)
                if q is not None and q == (c, want):
                    return ('ev', n)
            return None
        if sers:
            return ('ev', sers[-1])
        X = self.X
        if c in X.sig.pre:
            return ('pre', X.sig.pre.index(c))
        cands = []
        for r in sorted(st.rs, reverse=True):
            R = st.rs[r]
            if all(C.expOf(c[0], b) >= e for b, e in R[0][0]):
                f = self.in_run(st, R, c)
                if f is not None:
                    if not f:
                        return ('run', r, [])
                    cands.append((len(f), r, f))
        if cands:
            _, r, f = min(cands)
            return ('run', r, f)
        a = C.srcOf(st, c)
        if a is not None:
            for n in sorted(st.pf, reverse=True):
                p = st.pf[n]
                if p[0] == a and c[1] in p[1]:
                    return ('pf', n)
            for r in sorted(st.pr, reverse=True):
                p = st.pr[r]
                if c[1] in p[1]:
                    f = self.in_run(st, p[0], a)
                    if f is not None:
                        return ('pfr', r, f)
        # residuals placing the cell in a run in scope (`sub`, `subR`)
        for i, res, wr in self.on(self.pool_sub):
            if res[0] == 'sub' and res[1] == c:
                R = C.runF(st.env, res[2])
                for r, R2 in st.rs.items():
                    if R2 == R:
                        return ('run', r, [self.use(i, wr)])
            elif res[0] == 'subR':
                R = C.runF(st.env, res[2])
                q = C.runF(st.env, res[1])
                f = self.in_run(st, q, c)
                if f is None:
                    continue
                for r, R2 in st.rs.items():
                    if R2 == R:
                        return ('run', r, sorted(set(f + [self.use(i, wr)])))
        return None

    def run1(self, st, Q):
        """A run needed, one part (`runOk1`): a run in scope, a residual `subR`, empty, its points."""
        for r in sorted(st.rs, reverse=True):
            f = self.run_in(st, Q, st.rs[r])
            if f is not None:
                return [('run', r, f)]
        for i, res, wr in self.on(self.pool_sub):
            if res[0] == 'subR' and C.runF(st.env, res[1]) == Q:
                R = C.runF(st.env, res[2])
                for r, R2 in st.rs.items():
                    if R2 == R:
                        return [('run', r, [self.use(i, wr)])]
        if C.emptyR(Q):
            return [('empty',)]
        if C.constR(Q) and Q[3][1] - Q[2][1] <= PTSMAX:
            ws = [('pts',)]
            for j in range(Q[2][1], Q[3][1]):
                w = self.pt(st, C.cshift(Q[0], Q[1] * j))
                if w is None:
                    return None
                ws.append(w)
            return ws
        return None

    def run(self, st, Q):
        """A run needed (`runOk`): one part, `cat k`, `mrg S`."""
        ws = self.run1(st, Q)
        if ws is not None:
            return ws
        base, S0, lo, hi = Q
        # `cat k`: split at a constant index where a run in scope of this base starts or ends
        ks = set()
        for R in st.rs.values():
            if R[0][0] == base[0] and R[1] == S0:
                for b in (R[2], R[3]):
                    if not b[0] and S0 and (R[0][1] - base[1]) % S0 == 0 and R[0][1] >= base[1]:
                        ks.add(b[1] + (R[0][1] - base[1]) // S0)
        for k in sorted(ks):
            if not lo[0] and k <= lo[1] or not hi[0] and k >= hi[1]:
                continue
            a = self.run1(st, (base, S0, lo, ((), k)))
            b = self.run1(st, (base, S0, ((), k), hi)) if a is not None else None
            if b is not None:
                self.stats['cat'] += 1
                return [('cat', k)] + a + b
        # `mrg S`: the residue runs of a stride in scope
        Ss = sorted({R[1] // S0 for R in st.rs.values() if R[0][0] == base[0] and S0 and R[1] % S0 == 0
                     and R[1] > S0})
        for S in Ss:
            if lo[0] or lo[1] % S or lo[1] >= C.CAPE:
                continue
            rt = C.rootC(hi, S)
            if C.cpow(rt, S) != hi:
                continue
            f = self.factE(st, rt)
            if f is None:
                continue
            ws = [('mrg', S, f)]
            for r in range(S):
                w = self.run1(st, C.mrgPart(Q, S, r, ((), lo[1] // S), rt))
                if w is None:
                    break
                ws += w
            else:
                self.stats['mrg'] += 1
                return ws
        return None

    def ptr(self, st, c, offs):
        """A pointer fact needed (`ptrOk`)."""
        for n in sorted(st.pf, reverse=True):
            p = st.pf[n]
            if p[0] == c and C.subL(offs, p[1]):
                return [('pf', n)]
        for r in sorted(st.pr, reverse=True):
            p = st.pr[r]
            if C.subL(offs, p[1]):
                f = self.in_run(st, p[0], c)
                if f is not None:
                    return [('pfr', r, f)]
        for n in sorted(st.sv):
            q = st.sv[n]
            if q[0] == c:
                ws = [('word', n)]
                for o in offs:
                    w = self.pt(st, C.cshift(q[1], o))
                    if w is None:
                        break
                    ws.append(w)
                else:
                    return ws
        return None

    def ptrR(self, st, Q, offs):
        """A pointer run needed (`ptrROk`)."""
        for r in sorted(st.pr, reverse=True):
            p = st.pr[r]
            if C.subL(offs, p[1]):
                f = self.run_in(st, Q, p[0])
                if f is not None:
                    return [('pfr', r, f)]
        if C.emptyR(Q):
            return [('empty',)]
        if C.constR(Q) and Q[3][1] - Q[2][1] <= PTSMAX:
            ws = [('pts',)]
            for j in range(Q[2][1], Q[3][1]):
                w = self.ptr(st, C.cshift(Q[0], Q[1] * j), offs)
                if w is None:
                    return None
                ws += w
            return ws
        return None

    def reqs(self, st, ms, G, where):
        """Witnesses of a signature's preconditions at the slots `ms`."""
        ws = []
        for c in G.pre:
            t = C.instC(ms, c)
            w = self.pt(st, t) if t is not None else None
            if w is None:
                self.miss.append((where, 'pre', t))
                return None
            ws.append(w)
        for r in G.preR:
            t = C.instR(ms, r)
            w = self.run(st, t) if t is not None else None
            if w is None:
                self.miss.append((where, 'preR', t))
                return None
            ws += w
        for c, offs in G.preP:
            t = C.instC(ms, c)
            w = self.ptr(st, t, offs) if t is not None else None
            if w is None:
                self.miss.append((where, 'preP', t, offs))
                return None
            ws += w
        for r, offs in G.prePR:
            t = C.instR(ms, r)
            w = self.ptrR(st, t, offs) if t is not None else None
            if w is None:
                self.miss.append((where, 'prePR', t, offs))
                return None
            ws += w
        return ws

    # -- the pass's hooks
    def is_read(self, key):
        return key in self.P.reads

    def read(self, pas, st, c, d, key):
        if key in self.H.reads:
            w = self.H.reads[key]
            return w if C.ptOk(self.X, st, c, w) else None
        want = self.envrec.get(d)
        w = None
        if want is not None and d not in st.env:
            try:
                want = cell(want)
            except Unsupported:
                want = None
            if want is not None and want != C.baseC(d):
                w = self.pt(st, c, want=want)
                if w is not None:
                    self.H.hvs.append(d)
                    self.X.hv.add(d)
                    self.stats['hv'] += 1
        if w is None:
            w = self.pt(st, c)
        if w is None:
            self.miss.append(('read', key, c))
        self.H.reads[key] = w if w is not None else ('fail',)
        return w

    def div(self, pas, st, d, x, y):
        for q, b in ((x, y), (y, x)):
            if q in st.env or q in self.X.dv:
                continue
            want = self.envrec.get(q)
            md, mb = st.env.get(d), C.mono(st.env, b)
            if want is None or md is None or mb[0] or mb[1] > md[1]:
                continue
            if (md[0], md[1] - mb[1]) == want:
                self.H.divs.append(q)
                self.X.dv.add(q)
                self.stats['div'] += 1
                return

    def ghosts(self, g, args):
        """The callee's ghost monomials at this call (`gargs`, by callee and arguments)."""
        G = self.X.sigOf(g)
        if not G.ghosts:
            return
        if any(p[0] == g and list(p[1]) == list(args) for p in self.H.gargs):
            return
        gis = self.sites.get((I.callee(g), tuple(args)), [])
        gi = gis[0] if gis else None
        if gi is None or len(gi) != G.ghosts or any(x is None for x in gi):
            self.miss.append(('ghosts', g, gi))
            return
        try:
            ms = [cell(x) for x in gi]
        except Unsupported:
            self.miss.append(('ghosts', g, gi))
            return
        self.H.gargs.append((g, list(args), ms))

    def call(self, pas, st, site, g, args, ma):
        self.ghosts(g, args)
        ga = C.gargsOf(self.H.gargs, g, args)
        ws = self.reqs(st, ma + ga, self.X.sigOf(g), site)
        assert len(self.H.calls) == st.nc, (len(self.H.calls), st.nc)
        self.H.calls.append(ws if ws is not None else [('fail',)])
        return ws

    def dispatch(self, pas, st, x, fs, args, ma, mx):
        ws = []
        ok = True
        for j, g in enumerate(fs):
            f = self.factU(st, mx, j)
            if f is not None:
                ws.append(('skip', f))
                self.stats['skip'] += 1
                continue
            self.ghosts(g, args)
            ga = C.gargsOf(self.H.gargs, g, args)
            w = pas.under(('arm', x, j), lambda: self.reqs(C.condSt(mx, j, st.cd, st), ma + ga, self.X.sigOf(g),
                                                           ('dispatch', g, j)))
            if w is None:
                ok = False
                continue
            ws += w
        assert len(self.H.calls) == st.nc
        self.H.calls.append(ws if ok else [('fail',)])
        return ws if ok else None

    def ret(self, pas, st, ms):
        G = self.X.sig
        ws = []
        pv = dict(G.postV)
        for i, c in enumerate(G.post):
            t = C.instC(ms, c)
            want = C.instC(ms, pv[i]) if i in pv else None
            w = self.pt(st, t, want=want) if t is not None else None
            if w is None and want is not None:
                self.miss.append(('ret', 'postV', t, want))
                return self.ret_done(None)
            if w is None:
                self.miss.append(('ret', 'post', t))
                return self.ret_done(None)
            ws.append(w)
        for r in G.postR:
            t = C.instR(ms, r)
            w = self.run(st, t) if t is not None else None
            if w is None:
                self.miss.append(('ret', 'postR', t))
                return self.ret_done(None)
            ws += w
        for c, offs in G.postP:
            t = C.instC(ms, c)
            w = self.ptr(st, t, offs) if t is not None else None
            if w is None:
                self.miss.append(('ret', 'postP', t, offs))
                return self.ret_done(None)
            ws += w
        for r, offs in G.postPR:
            t = C.instR(ms, r)
            w = self.ptrR(st, t, offs) if t is not None else None
            if w is None:
                self.miss.append(('ret', 'postPR', t, offs))
                return self.ret_done(None)
            ws += w
        return self.ret_done(ws)

    def ret_done(self, ws):
        self.H.rets.append(ws if ws is not None else [('fail',)])
        return ws

    def tail(self, pas, st, mp, mx, ex, ei):
        G = self.X.sig
        X = self.X
        ws = []
        for c in G.post:
            w = None
            for ms in [mp] + ([mx] if ex and C.noSlot0(c) else []):
                t = C.instC(ms, c)
                w = self.pt(st, t) if t is not None else None
                if w is not None:
                    break
            if w is None:
                self.miss.append(('tail', 'post', c))
                return self.ret_done(None)
            ws.append(w)
        for r in G.postR:
            w = None
            for ms in [mp] + ([mx] if ex and C.noSlot0R(r) else []):
                q = C.instR(ms, r)
                w1 = self.run1(st, q) if q is not None else None
                if w1 is not None and len(w1) == 1:
                    w = w1[0]
                    break
            if w is None and r[2] == ('val', 0) and r[3] == ei and C.noSlot0(r[0]):
                b = C.instC(mp, r[0])
                if b is not None:
                    w = self.pt(st, C.cmul(b, C.cpow(mp[0], r[1])))
            if w is None:
                self.miss.append(('tail', 'postR', r))
                return self.ret_done(None)
            ws.append(w)
        for p in G.postP:
            w = None
            for ms in [mp] + ([mx] if ex and C.noSlot0(p[0]) else []):
                t = C.instC(ms, p[0])
                w = self.ptr(st, t, p[1]) if t is not None else None
                if w is not None:
                    break
            if w is None:
                self.miss.append(('tail', 'postP', p))
                return self.ret_done(None)
            ws += w
        for p in G.postPR:
            w = None
            for ms in [mp] + ([mx] if ex and C.noSlot0R(p[0]) else []):
                q = C.instR(ms, p[0])
                w = self.ptrR(st, q, p[1]) if q is not None else None
                if w is not None:
                    break
            if w is None and p[0][2] == ('val', 0) and p[0][3] == ei and C.noSlot0(p[0][0]):
                b = C.instC(mp, p[0][0])
                if b is not None:
                    w = self.ptr(st, C.cmul(b, C.cpow(mp[0], p[0][1])), p[1])
            if w is None:
                self.miss.append(('tail', 'postPR', p))
                return self.ret_done(None)
            ws += w
        return self.ret_done(ws)


# ---- one function

def solve(k, P, sigs, sigOf):
    params, body = I.CORE[k]
    H = C.HCert(sigs[k])
    S = Solver(k, P, H, sigs)
    S.miss = []
    X_ = C.X(dict(I.POWS), H, sigOf, params, S)
    S.X = X_
    # `heapc.heapOkC` builds its own `X`: run the pass on ours
    pas = run_pass(X_, params, body)
    H.res = list(H.res)
    return H, S, pas


def run_pass(X_, params, body):
    """`heapc.heapOkC` with a given context (its solver's)."""
    G = X_.sig
    P = C.Pass(X_, X_.sigOf, body)
    m = len(params)
    if list(params) != list(range(m)):
        P.fail('params')
    if not all(b < m for c in G.pre for b, _ in c[0]):
        P.fail('preOver')
    if not all(C.idxOver(m, a) and C.idxOver(m, b) for a, b in G.term):
        P.fail('term-over')
    st = C.St()
    for i in range(m):
        st.env[i] = C.baseC(i)
    ms = C.monos(st.env, params) + [C.baseC(C.GB + j) for j in range(G.ghosts)]
    pps, rs, prs = C.instPP(ms, G.preP), C.instAllR(ms, G.preR), C.instPRL(ms, G.prePR)
    if pps is None or rs is None or prs is None:
        P.fail('init-inst')
        return P
    for p in pps:
        st.pushP(p)
    for r in rs:
        st.pushR(r)
    for p in prs:
        st.pushPR(p)
    if not G.term:
        P.block(body, st)
    elif len(G.term) == 1 and G.term[0][0] == ('val', 0) and (G.term[0][1] == ('val', 1) or G.term[0][1][0] == 'num'):
        if G.retM or G.postV:
            P.fail('loop-retM-postV')
        ei = G.term[0][1]
        if len(body) < 2 or body[-1] != ('ret', []) or body[-2][0] != 'callIf':
            P.fail('loop-shape')
            return P
        _, c, g, args = body[-2]
        st = P.block(body[:-2], st)
        P.callIf(st, c, g, args)
        P.tail(st, args, ei)
    else:
        P.fail('term-shape', G.term)
    return P


def check(k, H, sigOf):
    params, body = I.CORE[k]
    try:
        C.heapOkC(dict(I.POWS), sigOf, k, params, body, H)
        return None
    except C.Fail as e:
        return e.args[0]


# ---- Lean text

def lcell(c):
    return '⟨[' + ', '.join(f'({b}, {e})' for b, e in c[0]) + f'], {c[1]}⟩'


def lidx(i):
    if i[0] == 'mono':
        return f'(.mono {lcell(i[1])})'
    return f'(.{i[0]} {i[1]})'


def lrun(r):
    return f'⟨{lcell(r[0])}, {r[1]}, {lidx(r[2])}, {lidx(r[3])}⟩'


def lcond(c):
    return f'.{c[0]} ' + ' '.join(str(x) for x in c[1:])


def lres(r):
    if r[0] == 'under':
        return f'.under [{", ".join(map(lcond, r[1]))}] ({lres(r[2])})'
    if r[0] == 'lt':
        return f'.lt {lidx(r[1])} {lidx(r[2])}'
    if r[0] == 'sub':
        return f'.sub {lcell(r[1])} {lrun(r[2])}'
    return f'.subR {lrun(r[1])} {lrun(r[2])}'


def lnums(l, ind='        '):
    return '[' + wrap((str(x) for x in l), ind) + ']'


def lwit(w):
    k = w[0]
    if k in ('ev', 'pre', 'pf', 'word', 'cat'):
        return f'.{k} {w[1]}'
    if k in ('run', 'pfr'):
        return f'.{k} {w[1]} {lnums(w[2])}'
    if k == 'skip':
        return f'.skip {lnums(w[1])}'
    if k == 'mrg':
        return f'.mrg {w[1]} {lnums(w[2])}'
    if k in ('pts', 'empty'):
        return f'.{k}'
    raise ValueError(w)


def wrap(items, ind='    ', width=110):
    lines, cur = [], ''
    for it in items:
        if cur and len(ind) + len(cur) + len(it) + 2 > width:
            lines.append(cur + ',')
            cur = ''
        cur = f'{cur}, {it}' if cur else it
    if cur:
        lines.append(cur)
    return ('\n' + ind).join(lines)


LIM = 16000   # characters of list text per declaration (each is elaborated within the default heartbeats)


class Aux:
    """Auxiliary declarations: a long list split into chunks, each its own `def`."""

    def __init__(self):
        self.defs = []

    def lst(self, name, typ, items, ind='    '):
        items = list(items)
        if sum(len(x) + 2 for x in items) <= LIM:
            return '[' + wrap(items, ind) + ']'
        parts, cur, n = [], [], 0
        for x in items:
            if cur and n + len(x) > LIM:
                parts.append(cur)
                cur, n = [], 0
            cur.append(x)
            n += len(x) + 2
        if cur:
            parts.append(cur)
        names = []
        for i, part in enumerate(parts):
            nm = f'{name}{i}'
            self.defs.append(f'def {nm} : List {typ} :=\n  [{wrap(part, "    ")}]\n')
            names.append(nm)
        return '(' + ' ++ '.join(names) + ')'


def lsig(G, ax):
    fs = []
    for f in ('pre', 'post'):
        if getattr(G, f):
            fs.append(f'{f} := ' + ax.lst(f'sig_{f}', 'CoreMode.CCell', map(lcell, getattr(G, f)), '        '))
    for f in ('preR', 'postR'):
        if getattr(G, f):
            fs.append(f'{f} := ' + ax.lst(f'sig_{f}', 'CoreMode.CRun', map(lrun, getattr(G, f)), '        '))
    if G.term:
        fs.append('«term» := [' + ', '.join(f'({lidx(a)}, {lidx(b)})' for a, b in G.term) + ']')
    if G.retM:
        fs.append('retM := ' + ax.lst('sig_retM', '(ℕ × CoreMode.CCell)', (f'({k}, {lcell(c)})' for k, c in G.retM),
                                     '        '))
    for f in ('preP', 'postP'):
        if getattr(G, f):
            fs.append(f'{f} := ' + ax.lst(f'sig_{f}', '(CoreMode.CCell × List ℕ)',
                                          (f'({lcell(c)}, {lnums(o)})' for c, o in getattr(G, f)), '        '))
    for f in ('prePR', 'postPR'):
        if getattr(G, f):
            fs.append(f'{f} := ' + ax.lst(f'sig_{f}', '(CoreMode.CRun × List ℕ)',
                                          (f'({lrun(r)}, {lnums(o)})' for r, o in getattr(G, f)), '        '))
    if G.postV:
        fs.append('postV := ' + ax.lst('sig_postV', '(ℕ × CoreMode.CCell)', (f'({i}, {lcell(c)})' for i, c in G.postV),
                                      '        '))
    if G.ghosts:
        fs.append(f'ghosts := {G.ghosts}')
    if not fs:
        return '{}'
    return '\n    { ' + ',\n      '.join(fs) + ' }'


def lwits(ax, name, ws):
    return ax.lst(name, 'CoreMode.Wit', map(lwit, ws), '        ')


def lcert(H, sig_only=False):
    """The aux declarations and the certificate's fields."""
    ax = Aux()
    out = f'  sig := {lsig(H.sig, ax)}\n'
    if sig_only:
        return ax.defs, out + '  reads := []\n  res := []\n'
    by_d = collections.defaultdict(list)
    for (d, p, off), w in sorted(H.reads.items()):
        by_d[d].append(f'({p}, {off}, {lwit(w)})')
    out += '  reads := ' + ax.lst('reads', '(ℕ × List (ℕ × ℕ × CoreMode.Wit))',
                                  (f'({d}, [{", ".join(rs)}])' for d, rs in sorted(by_d.items()))) + '\n'
    out += '  res := ' + ax.lst('res', 'CoreMode.CRes', map(lres, H.res)) + '\n'
    if H.calls:
        out += '  calls := ' + ax.lst('calls', '(List CoreMode.Wit)',
                                      [lwits(ax, f'call{i}_', ws) for i, ws in enumerate(H.calls)]) + '\n'
    if H.rets:
        out += '  rets := ' + ax.lst('rets', '(List CoreMode.Wit)',
                                     [lwits(ax, f'ret{i}_', ws) for i, ws in enumerate(H.rets)]) + '\n'
    if H.divs:
        out += f'  divs := {lnums(sorted(H.divs))}\n'
    if H.hvs:
        out += '  hvs := ' + ax.lst('hvs', 'ℕ', map(str, sorted(H.hvs))) + '\n'
    if H.gargs:
        out += '  gargs := [' + wrap((f'("{g}", {lnums(a)}, [{", ".join(map(lcell, ms))}])' for g, a, ms in H.gargs)) + ']\n'
    return ax.defs, out


def pack_of():
    out = {}
    for p in glob.glob(os.path.join(GUEST, 'Pack', '*', 'Core*.lean')):
        pack = os.path.basename(os.path.dirname(p))
        text = open(p, encoding='utf-8').read()
        ms = list(re.finditer(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', text, re.M))
        for i, m in enumerate(ms):
            # the module that defines the function's `core` (a split body's parts come first in no order)
            end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
            has = re.search(r'^noncomputable def core : Core\.Fn', text[m.end():end], re.M) is not None
            prev = out.get(m.group(1))
            if prev is None or has and not prev[2]:
                out[m.group(1)] = (pack, os.path.basename(p)[:-5], has)
    return {k: v[:2] for k, v in out.items()}


HEADER = '''/-
  LeanVM.Guest.CoreMode.GenC.«{pack}».{mod}

  Generated by `scripts/core-mode/emitc.py`; do not edit.
  {what}
-/

module

'''


def build(res, only=None):
    """Every function's signature, certificate and the Python check's verdict."""
    sigs, drops = {}, {}
    for k in I.ORDER:
        dr = []
        sigs[k] = sig_of(I.SIGS[k], len(I.CORE[k][0]), dr)
        if dr:
            drops[k] = dr
    stmt_names = collections.defaultdict(set)
    for k in I.CORE:
        for s in I.stmts(I.CORE[k][1]):
            if s[0] == 'call':
                stmt_names[k].add(s[1])
            elif s[0] == 'callIf':
                stmt_names[k].add(s[2])
            elif s[0] == 'dispatch':
                stmt_names[k].update(s[2])

    def sigOf(g):
        return sigs.get(I.callee(g), C.EMPTY)
    certs, why, stats = {}, {}, collections.Counter()
    for k in I.ORDER:
        if only and k not in only:
            continue
        P = res[k]
        H, S, pas = solve(k, P, sigs, sigOf)
        stats.update(S.stats)
        certs[k] = H
        fails = list(pas.fails) + [('miss',) + m for m in S.miss]
        if not fails:
            e = check(k, H, sigOf)
            if e is not None:
                fails = [('recheck', e)]
        if fails:
            why[k] = fails
    return sigs, certs, why, drops, stmt_names, stats


def cause(k, fails, P):
    """A failure's class, for the report."""
    f = fails[0]
    return f[0] if f[0] != 'miss' else 'miss:' + str(f[1][0] if isinstance(f[1], tuple) else f[1]) + ':' + str(f[2] if len(f) > 2 and isinstance(f[2], str) else '')


def emit(out, res, check_only, only=None):
    sigs, certs, why, drops, stmt_names, stats = build(res, only)
    passing = {k for k in certs if k not in why}
    closed = set()
    for k in I.ORDER:
        if k in passing and all(c in closed for c in I.CALLS[k] if c != k and c in I.CORE):
            closed.add(k)
    po = pack_of()
    packs = collections.defaultdict(list)
    for k in sorted(certs):
        packs[po[k][0]].append(k)
    stale, mods, lines = [], [], 0
    for pack, ks in sorted(packs.items()):
        d = os.path.join(out, pack)
        data = HEADER.format(pack=pack, mod='Data', what=f'The heap certificates of `{ks[0]}` and {len(ks) - 1} more.')
        data += 'public import LeanVM.Guest.CoreMode.Defs\n\nset_option maxRecDepth 100000\nset_option linter.all false\n'
        oks = [k for k in ks if k in passing and k not in KERNEL_SKIP]
        cal = lambda k: sorted({I.callee(n) for n in stmt_names[k]} & set(I.CORE))
        imps = sorted({f'LeanVM.Guest.Pack.«{pack}».{po[k][1]}' for k in oks} |
                      {f'LeanVM.Guest.CoreMode.GenC.«{po[c][0]}».Data' for k in oks for c in cal(k)})
        ok = HEADER.format(pack=pack, mod='Ok', what=f'The kernel\'s heap checks of {len(oks)} functions.')
        ok += 'public import LeanVM.Guest.CoreMode.HeapC\npublic import LeanVM.Guest.Data.Pows\n'
        ok += ''.join(f'public import {m}\n' for m in imps)
        ok += f'public import LeanVM.Guest.CoreMode.GenC.«{pack}».Data\n\nset_option Elab.async false\n'
        for k in ks:
            aux, body = lcert(certs[k], sig_only=k not in passing)
            auxt = ''.join(f'/-- Part of `hcert`. -/\n{d}\n' for d in aux)
            data += (f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n{auxt}'
                     f'/-- `{k}`: its heap certificate{"" if k in passing else " (its signature only: not checked)"}. -/\n'
                     f'def hcert : CoreMode.HCert where\n{body}\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        for k in oks:
            names = sorted(stmt_names[k])
            arms = ''.join(f'\n    | "{n}" => Fn.«{I.callee(n)}».hcert.sig' for n in names if I.callee(n) in I.CORE)
            sig = f'(fun g ↦ match g with{arms}\n    | _ => .empty)' if arms else '(fun _ ↦ .empty)'
            ok += (f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n/-- `{k}`: the heap check. -/\n'
                   f'theorem heap_okC : CoreMode.heapOkC Data.powTree\n    {sig}\n    core hcert = true := by\n'
                   f'  decide +kernel\n\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        files = [('Data', data)] + ([('Ok', ok)] if oks else [])
        for name, text in files:
            path = os.path.join(d, name + '.lean')
            lines += text.count('\n')
            mods.append(f'LeanVM.Guest.CoreMode.GenC.«{pack}».{name}')
            if check_only:
                if not os.path.exists(path) or open(path, encoding='utf-8').read() != text:
                    stale.append(path)
            else:
                os.makedirs(d, exist_ok=True)
                with open(path, 'w', encoding='utf-8') as fh:
                    fh.write(text)
    if check_only and not only:
        have = set(glob.glob(os.path.join(out, '*', '*.lean')))
        want = {os.path.join(out, m.split('«')[1].split('»')[0], m.rsplit('.', 1)[1] + '.lean') for m in mods}
        stale += sorted(have - want)
    elif not only:
        want = {os.path.join(out, m.split('«')[1].split('»')[0], m.rsplit('.', 1)[1] + '.lean') for m in mods}
        for p in set(glob.glob(os.path.join(out, '*', '*.lean'))) - want:
            os.remove(p)
    clean, inf_closed = I.closure(res)
    cw = collections.Counter(cause(k, why[k], res[k]) for k in why)
    print(f'certificates: {len(certs)}; the Python check passes {len(passing)} (closed, callees too: {len(closed)}); '
          f'the inference closes {len(inf_closed)}, of which pass {len(passing & inf_closed)}; '
          f'{len(packs)} packs, {lines} lines')
    print('  failures by first cause:', dict(cw.most_common()))
    print('  of the inference\'s closed:', dict(collections.Counter(cause(k, why[k], res[k]) for k in why
                                                                     if k in inf_closed).most_common()))
    print('  signature entries dropped:', dict(collections.Counter(x[0] for v in drops.values() for x in v)))
    print('  solver:', dict(stats))
    if check_only and not only:
        print(f'checked: ' + (f'{len(stale)} stale: {stale[:5]}' if stale else 'up to date'))
        if stale:
            sys.exit(1)
    if '--report' in argv:
        with open(argv[argv.index('--report') + 1], 'w') as fh:
            json.dump({k: [repr(f) for f in v[:20]] for k, v in why.items()}, fh, indent=0)
    return mods, certs, why


def main():
    if '--lean' not in argv and '--with' not in argv:
        I.F.difference_update(OFF)
    I.set_features(argv)
    res, dt = I.run_all()
    print(f'inferred {len(res)} functions in {dt:.1f} s, features: {",".join(sorted(I.F)) or "(none)"}')
    out = argv[argv.index('--out') + 1] if '--out' in argv else os.path.join(GUEST, 'CoreMode', 'GenC')
    only = set(argv[argv.index('--fn') + 1].split(',')) if '--fn' in argv else None
    mods, certs, why = emit(out, res, '--check' in argv or only is not None, only)
    if only:
        for k in sorted(only):
            print(k, 'PASS' if k not in why else why[k][:10])
    if '--mods' in argv:
        with open(argv[argv.index('--mods') + 1], 'w') as fh:
            fh.write('\n'.join(mods) + '\n')


if __name__ == '__main__':
    main()
