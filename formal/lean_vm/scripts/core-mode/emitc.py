"""The heap certificates of `infer.py` in `heapOkC`'s input format (`m2-format.md`, `CoreMode/Defs.lean`), and their
checks.

The inference gives each function's signature and residuals; the witnesses are then found in `heapOkC`'s own pass
(`heapc.py`, the check in Python step for step): each read, callee precondition and own guarantee gets a witness of
the check's scope (an event's serial, a precondition, a run or pointer fact or pointer run in scope with the residuals
it needs, `pts`, `cat`, `mrg`, `word`, `skip`), so serials, joins and selector guarantees are the check's. The reads
taking a stored word (`hvs`), the quotients (`divs`) and the callees' ghost words (`gargs`) follow the inference's
values. What the check cannot witness is reported by cause; only functions the Python check passes get a kernel check.

Per pack: `LeanVM/Guest/CoreMode/GenC/<pack>/Data.lean`, every function's `hcert` (long lists split into auxiliary
`def`s, each elaborated within the default heartbeats); `Ok.lean`, `heap_okC : heapOkC Data.powTree sigOf core hcert =
true` for each function whose certificate the Python check passes and whose check is small enough for one `decide`
(the others are windowed: `heapwin.py`, `GenCW/<fn>/`), `sigOf` its callees' signatures by their `Fn.name`. Residuals
carry the branch conditions common to the paths the inference asked them on (`CRes.under`); a `mrg` whose root has no
exponent gets one stated (`exp`).

usage (from formal/lean_vm, `CORE_MODE_CACHE` set): python3 -I scripts/core-mode/emitc.py [--with F,..] [--without F,..]
  [--out DIR] [--check] [--mods FILE] [--fn NAME,..] (those functions only, nothing written) [--report FILE.json]
  (each failing function's causes)
"""
import sys, os, collections, glob, re, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
argv = list(sys.argv)
sys.argv = sys.argv[:1]
import infer as I
import heapc as C
if __name__ == '__main__':
    # `heapwin.py` imports this module by name: one instance (one `Pass` instrumentation)
    sys.modules.setdefault('emitc', sys.modules[__name__])

GUEST = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
NAME = {k: nm for nm, k in I.STABLE.items()}
# the inference's features `heapOkC` has no counterpart of, off by default: offsets modulo `g`'s order (cells are
# naturals there) and range checks as free facts (there every fact is a residual)
OFF = {'wrap', 'lts'}
PTSMAX = 4096
# functions checked in windows whatever their size (`heapwin.py`, `GenCW/<fn>/`); every other passing function whose
# check `heapwin.fn_cost` puts over `heapwin.BUDGET` (past the default heartbeats, or the memory a module may take, in
# one `decide`) is windowed too
KERNEL_WIN = {'main_loop2'}


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
    I.Pass.atom, I.Pass.call = atom, call


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


def mdivC(a, b):
    """The monomial `a / b` when `b` divides `a` (exponents and offset), else `None`."""
    da = dict(a[0])
    for x, e in b[0]:
        if da.get(x, 0) < e:
            return None
        da[x] -= e
    if a[1] < b[1]:
        return None
    return (tuple(sorted((x, e) for x, e in da.items() if e)), a[1] - b[1])


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
    H.postQ = each('postQ', getattr(G, 'postQ', ()), lambda p: (cell(p[0], m), crun(p[1], m)))

    def pv(p):
        c = cell(p[0], m)
        if c not in H.post:
            raise Unsupported(('postV-cell', p[0]))
        return (H.post.index(c), cell(p[1], m))
    H.postV = each('postV', G.postV, pv)
    H.ghosts = len(G.ghosts)
    H.retEq = each('retEq', getattr(G, 'retEq', ()), lambda p: (cell(p[0]), cell(p[1])))
    # a returned pointer's cells (`retP`): `post` cells over the returned slot
    for j, offs in sorted(getattr(G, 'retP', {}).items()):
        for o in sorted(offs):
            c = (((m + j, 1),), o)
            if c not in H.post:
                H.post.append(c)
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
    if k == 'subP':
        return ('subP', cell(r[1]), tuple(cell(c) for c in r[2]))
    return None


def ncell(env, c):
    """A cell over value numbers with each base's monomial in `env` (its word is the same)."""
    acc = ((), c[1])
    for b, e in c[0]:
        acc = C.cmul(acc, C.cpow(env.get(b, C.baseC(b)), e))
    return acc


def nidx(env, i):
    return ('mono', ncell(env, i[1])) if i[0] == 'mono' else i


def nrun(env, r):
    return (ncell(env, r[0]), r[1], nidx(env, r[2]), nidx(env, r[3]))


def nres(env, r):
    k = r[0]
    if k == 'lt':
        return ('lt', nidx(env, r[1]), nidx(env, r[2]))
    if k == 'sub':
        return ('sub', ncell(env, r[1]), nrun(env, r[2]))
    if k == 'subR':
        return ('subR', nrun(env, r[1]), nrun(env, r[2]))
    if k == 'subP':
        return ('subP', ncell(env, r[1]), tuple(ncell(env, c) for c in r[2]))
    return r


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
            # one copy per branch path it was asked on (`under` is a conjunction; a residual asked in two arms holds
            # in each under its own arm, not necessarily in both)
            gs = list(dict.fromkeys(conds_of([p]) for p in P.rpath.get(i, ()) or [()]))
            for g in gs:
                wr = ('under', g, r) if g else r
                (self.pool_lt if r[0] == 'lt' else self.pool_sub).append((i if len(gs) == 1 else (i, g), r, wr))
        self.sites = collections.defaultdict(list)
        for f, args, gi, _ in P.sites:
            self.sites[(f, tuple(args))].append(gi)
        self.envrec = P.__dict__.get('envrec', {})
        self.stats = collections.Counter()
        # returned words of calls, by value: the call's arguments (a returned cursor stays in a run an argument names)
        self.retargs = {}
        for s_ in C.stmts(I.CORE[k][1]):
            if s_[0] == 'call':
                for v in s_[3]:
                    self.retargs[v] = set(s_[2])

    # -- residuals and facts
    def on(self, pool, st):
        """The residuals usable on the site's path, their monomials over the check's own (a value's monomial in the
        check's environment for the value: one word, `idxF` takes `.mono` cells literally). Cached per pool, path and
        environment (which only grows)."""
        key = (id(pool), tuple(self.X.path), id(st.env), len(st.env))
        c = self.__dict__.setdefault('_on', {})
        if key not in c:
            if len(c) > 64:
                c.clear()
            c[key] = self.on0(pool, st)
        return c[key]

    def on0(self, pool, st):
        out = []
        for i, r, wr in pool:
            if C.unU(self.X.path, wr) is None:
                continue
            r2 = nres(st.env, r)
            if r2 != r:
                g = wr[1] if wr[0] == 'under' else ()
                i, r, wr = (i, r2), r2, (('under', g, r2) if g else r2)
            out.append((i, r, wr))
        return out

    def use(self, i, r):
        j = self.lean_res.get(i)
        if j is None:
            j = self.lean_res[i] = len(self.H.res)
            self.H.res.append(r)
        return j

    def fidx(self, st):
        """The facts usable at the site, own (source `None`) then the residuals' `(i, wr)`, indexed by each side
        (cached per path and environment, which only grows)."""
        key = (tuple(self.X.path), id(st.env), len(st.env))
        if getattr(self, '_fi', (None,))[0] != key:
            by_a, by_b = collections.defaultdict(list), collections.defaultdict(list)
            for p in self.X.facts(st.env, []):
                by_a[p[0]].append((p[1], None))
                by_b[p[1]].append((p[0], None))
            for i, r, wr in self.on(self.pool_lt, st):
                a, b = C.idxF(st.env, r[1]), C.idxF(st.env, r[2])
                by_a[a].append((b, (i, wr)))
                by_b[b].append((a, (i, wr)))
            self._fi = (key, by_a, by_b)
        return self._fi[1], self._fi[2]

    def src(self, x):
        return [] if x is None else [self.use(*x)]

    def fact(self, st, a, b):
        """Residuals giving the fact `(a, b)`: `[]` from the own term, `None` if none."""
        for a2, x in self.fidx(st)[1].get(b, ()):
            if a2 == a:
                return self.src(x)
        return None

    def idx(self, st, m):
        """A monomial as a residual's index (`.val` when the value's own base)."""
        if not m[0]:
            return ('num', m[1])
        if m[1] == 0 and len(m[0]) == 1 and m[0][0][1] == 1 and C.mono(st.env, m[0][0][0]) == m:
            return ('val', m[0][0][0])
        return ('mono', m)

    def derive(self, st, a, b, wr):
        """The fact `(a, b)` stated as a residual of its own, implied by a fact `(a', b)`, `a' = a·g^s` (`s >= 0`), the
        residual `wr` (under its conditions) or the own term or path (`None`)."""
        # under the site's whole path: the source's conditions are on it, and an arm fact holds only there
        g = tuple(dict.fromkeys(self.X.path))
        r = ('lt', self.idx(st, a), self.idx(st, b))
        self.stats['lt-derived'] += 1
        return [self.use(('lt', a, b, g), ('under', g, r) if g else r)]

    def factD(self, st, a, b):
        """`fact`, else a fact `(a·g^s, b)` (or `(g^k', b)`, `k' >= a` for a constant `a`) giving `(a, b)` stated."""
        f = self.fact(st, a, b)
        if f is not None:
            return f
        if a[1] >= C.CAPE:
            return None
        for a2, x in self.fidx(st)[1].get(b, ()):
            if a2[0] == a[0] and a[1] <= a2[1] < C.CAPE:
                return self.derive(st, a, b, x[1] if x else None)
        if not b[0] and b[1] < C.CAPE:
            # a constant bound a fact's smaller constant bound gives
            for b2, x in self.fidx(st)[0].get(a, ()):
                if not b2[0] and b2[1] <= b[1]:
                    return self.derive(st, a, b, x[1] if x else None)
            # `a = x·g^c` and a fact `e(x) < n`, `n + c <= b`
            if a[0] and a[1]:
                for b2, x in self.fidx(st)[0].get((a[0], 0), ()):
                    if not b2[0] and b2[1] + a[1] <= b[1]:
                        return self.derive(st, a, b, x[1] if x else None)
        if not b[0] and a[0] and b[1] < C.CAPE:
            # a fact `(a·g^-s, g^k)`, `k + s <= e(b)`: both sides shifted
            for b2, xs in self.fidx(st)[1].items():
                if b2[0]:
                    continue
                for a2, x in xs:
                    if a2[0] == a[0] and a2[1] <= a[1] and b2[1] + (a[1] - a2[1]) <= b[1]:
                        return self.derive(st, a, b, x[1] if x else None)
        return None

    def factC(self, st, k, b):
        """A fact `(g^k', b)`, `k <= k' < 2^62`."""
        for a2, x in self.fidx(st)[1].get(b, ()):
            if not a2[0] and k <= a2[1] < C.CAPE:
                return self.src(x)
        return None

    def factU(self, st, a, j):
        """A fact `(a, g^h)`, `h <= j`."""
        for b, x in self.fidx(st)[0].get(a, ()):
            if not b[0] and b[1] <= j:
                return self.src(x)
        return None

    def factU_eq(self, st, mx, j):
        """No fact `(mx, g^h)`, `h <= j`, but `mx·g^t = b` by a kept equation and a fact `(b, g^h')`, `h' - t <= j`: the
        bound `e(mx) < h' - t` stated (under the site's path). A constant selector `g^c`, `c < j`: `c < c + 1`."""
        if not mx[0] and mx[1] < j:
            return self.derive(st, mx, ((), mx[1] + 1), None)
        for a, b in st.eqs:
            for u, v in ((a, b), (b, a)):
                if u[0] != mx[0] or u[1] < mx[1]:
                    continue
                t = u[1] - mx[1]
                for b2, _ in self.fidx(st)[0].get(v, ()):
                    if not b2[0] and t <= b2[1] <= j + t:
                        return self.derive(st, mx, ((), b2[1] - t), None)
        return None

    def factE(self, st, m):
        """`m` has an exponent: a constant, or a side of a fact."""
        if not m[0] and m[1] < C.CAPE:
            return []
        for p in self.X.facts(st.env, []):
            if m in p:
                return []
        for i, r, wr in self.on(self.pool_lt, st):
            if C.idxF(st.env, r[1]) == m or C.idxF(st.env, r[2]) == m:
                return [self.use(i, wr)]
        # none: the inference's `merge` takes the root's exponent for granted; stated as a residual of its own
        # (`exp`: the word is `g^y`, `y < 2^62 - 1`)
        # (under the site's path: off it the value need not be computed)
        r = ('lt', ('val', m[0][0][0]) if m[1] == 0 and len(m[0]) == 1 and m[0][0][1] == 1 else ('mono', m),
             ('num', C.CAPE - 1))
        g = tuple(dict.fromkeys(self.X.path))
        self.stats['exp-res'] += 1
        return [self.use(('exp', m, g), ('under', g, r) if g else r)]

    # -- a cell of a run (`ptRun`), the residuals it needs
    def in_run(self, st, R, c):
        base, S, lo, hi = R
        if c == C.cmul(base, C.cpow(lo, S)):
            f = self.fact(st, lo, hi)
            if f is not None:
                return f
        J = C.idxOf(base, c, S)
        if c == C.cmul(base, C.cpow(J, S)) and (J[0] or not self.const_ok(st, R, c)):
            # (a constant index goes by the constant form below, whose fact `(g^k', hi)` serves every `k <= k'`)
            f = self.factD(st, J, hi)
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
                K = max(self.arm_above(st, k, hi), self.fact_shifted(st, k, hi))
                if K >= k:
                    # the largest bound the source gives, so one residual serves every cell below it
                    return self.derive(st, ((), K), hi, None)
        k = C.backK(R, c)
        if 0 < k and C.cshift(c, S * k) == C.cmul(base, C.cpow(hi, S)) and not lo[0] and lo[1] < C.CAPE:
            f = self.factC(st, k - 1 + lo[1], hi)
            if f is None:
                f = self.factD(st, ((), k - 1 + lo[1]), hi)
            if f is None and hi[0] and hi[1] > k - 1 + lo[1]:
                # `hi = m·g^t`, `t > k - 1 + lo`: the bound holds once `hi`'s exponent exists (`exp`)
                f = self.derive(st, ((), k - 1 + lo[1]), hi, None)
            if f is not None:
                self.stats['ptBack'] += 1
                return f
        return None

    def all_facts(self, st):
        """The usable facts as pairs."""
        return [(a, b) for a, l in self.fidx(st)[0].items() for b, _ in l]

    def fact_shifted(self, st, k, hi):
        """The largest `k' - s` of a fact `(g^k', hi·g^s)`: `e(hi) > k' - s` (`-1`: none)."""
        if not hi[0]:
            return -1
        K = -1
        for b, l in self.fidx(st)[1].items():
            if b[0] == hi[0] and b[1] >= hi[1]:
                for a, _ in l:
                    if not a[0] and a[1] < C.CAPE:
                        K = max(K, a[1] - (b[1] - hi[1]))
        return K

    def arm_above(self, st, k, hi):
        """On the site's path, an arm `j` of a selector `x` whose monomial times `g^t` is `hi` by a kept equation: then
        `e(hi) > j + t - 1` there (the residual is stated under the path); the largest such bound, `-1` if none."""
        K = -1
        for c in self.X.path:
            if c[0] != 'arm':
                continue
            mx = C.mono(st.env, c[1])
            for a, b in st.eqs:
                for u, v in ((a, b), (b, a)):
                    if v == hi and u[0] == mx[0] and u[1] >= mx[1]:
                        K = max(K, c[2] + u[1] - mx[1] - 1)
        return K

    def const_ok(self, st, R, c):
        """The constant form (`ptConst`) holds `c` by a constant bound or a fact in scope."""
        base, S, lo, hi = R
        if not (c[0] == base[0] and base[1] <= c[1] and S and (c[1] - base[1]) % S == 0 and not lo[0]
                and lo[1] < C.CAPE):
            return False
        k = (c[1] - base[1]) // S
        return lo[1] <= k and ((not hi[0] and hi[1] < C.CAPE and k < hi[1]) or self.factC(st, k, hi) is not None)

    def run_in(self, st, Q, R):
        """`runRun`: the run `Q` inside `R`, the residuals it needs."""
        if Q[0] != R[0] or Q[1] != R[1]:
            return None
        res = []
        if not (C.eqV(st.eqs, Q[2], R[2]) or (not Q[2][0] and not R[2][0] and R[2][1] <= Q[2][1] < C.CAPE)):
            if Q[2] != C.cshift(R[2], 1):
                return None
            f = self.fact(st, R[2], R[3])
            if f is None:
                return None
            res += f
        if not (C.eqV(st.eqs, Q[3], R[3]) or (not Q[3][0] and not R[3][0] and Q[3][1] <= R[3][1] < C.CAPE)):
            f = self.fact(st, Q[3], R[3])
            if f is None and Q[3][1] > 0:
                f = self.fact(st, (Q[3][0], Q[3][1] - 1), R[3])
            if f is None and not Q[3][0] and Q[3][1] < C.CAPE:
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
        # residuals placing the cell in a run in scope (`sub`, `subR`), among cells (`subP`)
        for i, res, wr in self.on(self.pool_sub, st):
            if res[0] == 'subP' and res[1] == c:
                ns = [st.c2s.get(x, (None,))[-1] for x in res[2]]
                if None not in ns:
                    self.stats['perm'] += 1
                    return ('perm', self.use(i, wr), ns)
                continue
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
        # a bounded index into points (`perm` over a fact `e(J) < n`: the cell is one of `Q·g^0..n-1`)
        w = self.pts_idx(st, c)
        if w is not None:
            return w
        # the point before a run (`prep`; that point possibly before another run)
        if depth < 2:
            w = self.prep(st, c, depth)
            if w is not None:
                return w
            w = self.app(st, c, depth)
            if w is not None:
                return w
        return self.cursor(st, c)

    def cursor(self, st, c):
        """`c = v·g^o`, `v` a word returned by a call one of whose arguments is the base of a long hint's run in scope
        (`hintRun`, the proof stream): a cursor the callee advanced through that run, the residual `sub c R` stated
        (under the site's path), its witness the run."""
        if len(c[0]) != 1 or c[0][0][1] != 1:
            return None
        args = self.retargs.get(c[0][0][0])
        if not args:
            return None
        for r in sorted(st.rs, reverse=True):
            R = st.rs[r]
            if R[1] != 1 or R[2] != ((), 0) or R[3][0] or R[3][1] < C.HINT_RUN or len(R[0][0]) != 1 or \
                    R[0][0][0][1] != 1 or R[0][1] or R[0][0][0][0] not in args:
                continue
            g = tuple(dict.fromkeys(self.X.path))
            Rr = (R[0], 1, ('num', 0), ('num', R[3][1]))
            if C.runF(st.env, Rr) != R:
                continue
            res = ('sub', c, Rr)
            self.stats['cursor'] += 1
            return ('run', r, [self.use(('cursor', c, Rr, g), ('under', g, res) if g else res)])
        return None

    def app(self, st, c, depth=0):
        """`app r q res`: `c` in run `r` extended by its point after it (`e(J) < e(hi·g)` a fact)."""
        for r in sorted(st.rs, reverse=True):
            R = st.rs[r]
            base, S, lo, hi = R
            if lo != ((), 0):
                continue
            J = C.idxOf(base, c, S)
            if c != C.cmul(base, C.cpow(J, S)):
                continue
            f = self.fact(st, J, C.cshift(hi, 1))
            if f is None:
                continue
            q = self.pt(st, C.appQ(R), depth=depth + 1)
            if q is None:
                continue
            self.stats['app'] += 1
            return ('app', r, q, f)
        return None

    def pts_idx(self, st, c):
        """`c = Q·J`, a fact `e(J) < n` (`n <= 64`) and the points `Q·g^i`, `i < n`, written: a residual `subP` (the cell
        is one of them, stated under the site's path), its witness `perm`."""
        cands = list(self.X.facts(st.env, []))
        for i, r, wr in self.on(self.pool_lt, st):
            cands.append((C.idxF(st.env, r[1]), C.idxF(st.env, r[2])))
        for a, b in cands:
            if b[0] or not a[0] or not 0 < b[1] <= 64:
                continue
            if any(C.expOf(c[0], k) < e for k, e in a[0]) or c[1] < a[1]:
                continue
            Q = (tuple((k, e - C.expOf(a[0], k)) for k, e in c[0] if e > C.expOf(a[0], k)), c[1] - a[1])
            if not Q[0] or C.cmul(Q, a) != c:
                continue
            cells = [C.cshift(Q, t) for t in range(b[1])]
            ns = [st.c2s.get(x, (None,))[-1] for x in cells]
            if None in ns:
                continue
            g = tuple(dict.fromkeys(self.X.path))
            r = ('subP', c, tuple(cells))
            self.stats['pts-idx'] += 1
            return ('perm', self.use(('subP', c, tuple(cells), g), ('under', g, r) if g else r), ns)
        return None

    def prep(self, st, c, depth=0):
        """`prep r q res`: `c` in run `r` extended by its point before it."""
        for r in sorted(st.rs, reverse=True):
            R = st.rs[r]
            base, S, lo, hi = R
            if lo != ((), 0) or S > base[1]:
                continue
            Q = C.prepQ(R)
            J = C.idxOf(Q, c, S)
            if c != C.cmul(Q, C.cpow(J, S)) or J[0] != hi[0] or J[1] > hi[1]:
                continue
            q = self.pt(st, Q, depth=depth + 1)
            if q is None:
                continue
            f = self.factE(st, hi)
            f2 = [] if J == hi else self.factE(st, J)
            self.stats['prep'] += 1
            return ('prep', r, q, sorted(set(f + f2)))
        return None

    def run1(self, st, Q):
        """A run needed, one part (`runOk1`): a run in scope, a residual `subR`, empty, its points."""
        for r in sorted(st.rs, reverse=True):
            f = self.run_in(st, Q, st.rs[r])
            if f is not None:
                return [('run', r, f)]
        for i, res, wr in self.on(self.pool_sub, st):
            if res[0] == 'subR' and C.runF(st.env, res[1]) == Q:
                R = C.runF(st.env, res[2])
                for r, R2 in st.rs.items():
                    if R2 == R:
                        return [('run', r, [self.use(i, wr)])]
        if C.emptyE(st.eqs, Q):
            return [('empty',)]
        w = self.suffix(st, Q)
        if w is not None:
            return w
        w = self.inner(st, Q)
        if w is not None:
            return w
        w = self.coarse(st, Q)
        if w is not None:
            return w
        if C.constR(Q) and Q[3][1] - Q[2][1] <= PTSMAX:
            ws = [('pts',)]
            for j in range(Q[2][1], Q[3][1]):
                w = self.pt(st, C.cshift(Q[0], Q[1] * j))
                if w is None:
                    return None
                ws.append(w)
            return ws
        return None

    def divides(self, st, h, H):
        """A kept equation `u = H` (either side) with `u = h·k`, `k` a monomial."""
        for a, b in st.eqs:
            for u, v in ((a, b), (b, a)):
                if v == H and u[1] >= h[1] and all(C.expOf(u[0], x) >= e for x, e in h[0]) and u != h:
                    return True
        return False

    def inner(self, st, Q):
        """A constant-bounds run of more than 8 cells whose first and last cells a run `R` in scope holds by the
        constant form (`ptConst`): the residual `subR Q R` (under the site's path), not one point witness a cell."""
        base, S, lo, hi = Q
        if not C.constR(Q) or hi[1] - lo[1] <= 8 or not S:
            return None
        first, last = C.cshift(base, S * lo[1]), C.cshift(base, S * (hi[1] - 1))
        for r in sorted(st.rs, reverse=True):
            R = st.rs[r]
            if R[1] != S or R[0][0] != base[0]:
                continue
            if not (self.const_ok(st, R, first) and self.const_ok(st, R, last)) and \
                    (self.in_run(st, R, first) is None or self.in_run(st, R, last) is None):
                continue
            g = tuple(dict.fromkeys(self.X.path))
            q = (base, S, ('num', lo[1]), ('num', hi[1]))
            Rr = (R[0], S, self.idx(st, R[2]), self.idx(st, R[3]))
            if C.runF(st.env, Rr) != R:
                continue
            res = ('subR', q, Rr)
            self.stats['inner'] += 1
            return [('run', r, [self.use(('inner', q, Rr, g), ('under', g, res) if g else res)])]
        return None

    def coarse(self, st, Q):
        """`Q = ⟨B·g^r, S, 0, h⟩`, `r < S`, the residue `r` of a run `⟨B, 1, 0, h^S⟩` in scope (`r + S·j < S·e(h)`): the
        residual `subR Q R` stated (under the site's path), its witness the run."""
        base, S, lo, hi = Q
        if S < 2 or lo != ((), 0) or not hi[0]:
            return None
        H = C.cpow(hi, S)
        for r in sorted(st.rs, reverse=True):
            R = st.rs[r]
            if R[1] != 1 or R[2] != ((), 0) or R[0][0] != base[0] or not 0 <= base[1] - R[0][1] < S or R[3] != H:
                continue
            g = tuple(dict.fromkeys(self.X.path))
            q = (base, S, ('num', 0), self.idx(st, hi))
            Rr = (R[0], 1, ('num', 0), self.idx(st, R[3]))
            if C.runF(st.env, q) != Q or C.runF(st.env, Rr) != R:
                continue
            res = ('subR', q, Rr)
            self.stats['coarse'] += 1
            return [('run', r, [self.use(('coarse', q, Rr, g), ('under', g, res) if g else res)])]
        return None

    def suffix(self, st, Q):
        """`Q = ⟨B·k^S, S, 0, h⟩` the part from `k` of a run `⟨B, S, 0, H⟩` in scope with `k·h = H` by the kept
        equations: the residual `subR Q R` stated (under the site's path), its witness the run."""
        base, S, lo, hi = Q
        if lo != ((), 0) or not st.eqs or not S:
            return None
        for r in sorted(st.rs, reverse=True):
            R = st.rs[r]
            if R[0] == base and R[1] == S and R[2] == lo and R != Q and self.divides(st, hi, R[3]):
                # a prefix: `R`'s upper bound `hi·k` by a kept equation
                g = tuple(dict.fromkeys(self.X.path))
                q, Rr = (base, S, ('num', 0), self.idx(st, hi)), (base, S, ('num', 0), self.idx(st, R[3]))
                if C.runF(st.env, q) == Q and C.runF(st.env, Rr) == R:
                    res = ('subR', q, Rr)
                    self.stats['prefix'] += 1
                    return [('run', r, [self.use(('prefix', q, Rr, g), ('under', g, res) if g else res)])]
            if R[1] != S or R[2] != ((), 0) or R[0][1] > base[1] or (base[1] - R[0][1]) % S or R == Q:
                continue
            if any(C.expOf(base[0], b) < e for b, e in R[0][0]):
                continue
            rest = tuple((b, e - C.expOf(R[0][0], b)) for b, e in base[0] if e > C.expOf(R[0][0], b))
            if not rest or any(e % S for _, e in rest):
                continue
            k = (tuple((b, e // S) for b, e in rest), (base[1] - R[0][1]) // S)
            if C.cmul(R[0], C.cpow(k, S)) != base or not C.eqV(st.eqs, C.cmul(k, hi), R[3]):
                continue
            g = tuple(dict.fromkeys(self.X.path))
            q = (base, S, ('num', 0), self.idx(st, hi))
            Rr = (R[0], S, ('num', 0), self.idx(st, R[3]))
            if C.runF(st.env, q) != Q or C.runF(st.env, Rr) != R:
                continue
            res = ('subR', q, Rr)
            self.stats['suffix'] += 1
            return [('run', r, [self.use(('suffix', q, Rr, g), ('under', g, res) if g else res)])]
        return None

    def run(self, st, Q, depth=0):
        """A run needed (`runOk`): `runOk0`, else `catM k h`: split at a symbolic index `k` where a run of this base
        ends, the part from it a run in scope (or, at the top, split once more: `runOkL`), `k·h` the upper bound by
        the kept equations."""
        ws = self.run0(st, Q)
        if ws is not None:
            return ws
        base, S0, lo, hi = Q
        if not S0:
            return None
        ks = []
        for R in st.rs.values():
            if R[0] == base and R[1] == S0:
                ks.append(R[3])
            elif R[0][0] == base[0] and R[1] % S0 == 0 and R[1] > S0 and R[0][1] == base[1]:
                ks.append(C.cpow(R[3], R[1] // S0))
            elif R[0][0] == base[0] and R[1] == S0 and S0 and R[0][1] > base[1] and (R[0][1] - base[1]) % S0 == 0 and \
                    R[2] == ((), 0) and hi[0]:
                # a run starting a constant index in: its points before it, split at `g^t`
                ks.append(((), (R[0][1] - base[1]) // S0))
            elif R[0][0] == base[0] and 0 <= base[1] - R[0][1] < S0 and R[1] == 1 and S0 > 1 and R[2] == ((), 0) and R[3][0] and R[3][1] % S0 == 0 and \
                    all(e % S0 == 0 for _, e in R[3][0]):
                # a stride-1 run whose bound is an `S0`-th power: its residue `0` (`coarse`) ends at the root
                ks.append((tuple((b, e // S0) for b, e in R[3][0]), R[3][1] // S0))
        for k in dict.fromkeys(ks):
            if k == hi or not k[0] and not k[1]:
                continue
            b2 = C.cmul(base, C.cpow(k, S0))
            hs = []
            for R in st.rs.values():
                if R[0] == b2 and R[1] == S0:
                    hs.append(R[3])
                elif R[0][0] == b2[0] and R[1] % S0 == 0 and R[1] > S0 and R[0][1] == b2[1]:
                    hs.append(C.cpow(R[3], R[1] // S0))
            # or the quotient of the bound by `k` (the part from `k` held otherwise: points, a merge)
            # the bound rewritten by a kept equation (`hi = M^t`, `M = N`: `N^t`), divided by `k`
            for hb in [hi] + [C.cpow(N, C.powK(M, hi)) for a_, b_ in st.eqs for M, N in ((a_, b_), (b_, a_))
                              if M[0] and C.cpow(M, C.powK(M, hi)) == hi]:
                q = mdivC(hb, k)
                if q is not None and q[0] is not None:
                    hs.append(q)
            for h in dict.fromkeys(hs):
                if not C.eqV(st.eqs, C.cmul(k, h), hi):
                    continue
                fk, fh = self.factE(st, k), self.factE(st, h)
                a = self.run0(st, (base, S0, lo, k))
                b = None
                if a is not None:
                    b = self.run0(st, (b2, S0, ((), 0), h)) if depth else self.run(st, (b2, S0, ((), 0), h), 1)
                if b is not None:
                    self.stats['catM'] += 1
                    return [('catM', k, h, sorted(set(fk + fh)))] + a + b
        return None

    def run0(self, st, Q):
        """A run needed, one level (`runOk0`): one part, `cat k`, `mrg S`, `mrgE S r`."""
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
                # `mrgE`: the root a residue run's bound, its `S`-th power the upper bound by the kept equations
                rts = [R[3] for R in st.rs.values() if R[0][0] == base[0] and R[1] == S0 * S and
                       C.eqV(st.eqs, C.cpow(R[3], S), hi)]
                fl = None
                if not rts:
                    # or a fact `(hi, r^S·g)`: the residues reach past the upper bound
                    for R in st.rs.values():
                        if R[0][0] == base[0] and R[1] == S0 * S and R[3][0]:
                            fl = self.fact(st, hi, C.cshift(C.cpow(R[3], S), 1))
                            if fl is not None:
                                rts = [R[3]]
                                break
                if not rts:
                    continue
                rt = rts[0]
                f = sorted(set(self.factE(st, rt) + (fl or [])))
                ws = [('mrgE', S, rt, f)]
                self.stats['mrgE'] += 1
            else:
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
        if C.emptyE(st.eqs, Q):
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

    def ghosts(self, g, args, st=None):
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
            # over the check's monomials (a value's monomial for the value: the same word)
            ms = [ncell(st.env, cell(x)) if st is not None else cell(x) for x in gi]
        except Unsupported:
            self.miss.append(('ghosts', g, gi))
            return
        self.H.gargs.append((g, list(args), ms))

    def call(self, pas, st, site, g, args, ma):
        self.ghosts(g, args, st)
        ga = C.gargsOf(self.H.gargs, g, args)
        ws = self.reqs(st, ma + ga, self.X.sigOf(g), site)
        assert len(self.H.calls) == st.nc, (len(self.H.calls), st.nc)
        self.H.calls.append(ws if ws is not None else [('fail',)])
        return ws

    def keeps(self, pas, st, st0, c, g, qs, ws):
        """`keep j b lo hi` and its witnesses: a guarantee run of a `callIf`'s callee (`CTR_PRE`, an exit guarantee)
        written where the call is not entered, rewritten by the guard's equation (`a = b`, `a` one base)."""
        if I.callee(g) not in I.CTR_PRE:
            return []
        p = st.ad.get(c)
        out = []
        for a, b in (p, (p[1], p[0])):
            if len(a[0]) != 1 or a[0][0][1] != 1 or a[1]:
                continue
            x = a[0][0][0]

            def sub(m):
                e = C.expOf(m[0], x)
                rest = (tuple((k, f) for k, f in m[0] if k != x), m[1])
                return C.cmul(rest, C.cpow(b, e))
            for j, q in enumerate(qs):
                if C.boundsOf(p, q):
                    continue
                bq, lo, hi = sub(q[0]), sub(q[2]), sub(q[3])
                if not (C.eqVM(st0.eqs, q[0], bq) and C.eqVM(st0.eqs, q[2], lo) and C.eqVM(st0.eqs, q[3], hi)):
                    continue
                saved = self.X.path
                self.X.path = [('zero', c)] + saved[1:]
                try:
                    w = self.run(st0, (bq, q[1], lo, hi))
                finally:
                    self.X.path = saved
                if w is not None:
                    out += [('keep', j, bq, lo, hi)] + w
                    self.stats['keep'] += 1
            if out:
                break
        return out

    def dispatch(self, pas, st, x, fs, args, ma, mx, rets=()):
        vps = [(j, self.P.vpoffs[v]) for j, v in enumerate(rets or ()) if v in getattr(self.P, 'vpoffs', {})]
        arms = []          # (skip witness) or (precondition witnesses, per vp the cells' witnesses or None)
        arms_j = [None] * len(fs)
        armj = []
        ok = True
        for j, g in enumerate(fs):
            f = self.factU(st, mx, j)
            if f is None:
                f = self.factU_eq(st, mx, j)
            if f is not None:
                arms.append(('skip', f))
                arms_j[j] = arms[-1]
                armj.append(j)
                self.stats['skip'] += 1
                continue
            self.ghosts(g, args, st)
            ga = C.gargsOf(self.H.gargs, g, args)
            sj = C.condSt(mx, j, st.cd, st)
            w = pas.under(('arm', x, j), lambda: self.reqs(sj, ma + ga, self.X.sigOf(g), ('dispatch', g, j)))
            if w is None:
                ok = False
                continue
            arms.append((w, pas.under(('arm', x, j), lambda: self.vp_arm(sj, ma, g, rets, vps))))
            arms_j[j] = arms[-1]
            armj.append(j)
        keep = [t for t, vp in enumerate(vps) if all(a[0] == 'skip' or a[1][t] is not None for a in arms)]
        # the arms' growing blocks (`ab`): arm `j` writes `⟨q, 1, 0, j + d⟩`
        abs_, abw = [], []
        blks = []
        for q, K, d in getattr(self.P, 'armblk', {}).get((x, tuple(fs), tuple(args)), ()):
            blks += [(C.cshift(cell(q), r), K, d // K) for r in range(K)]
        for q, K, d in blks:
            per = []
            for j, g in enumerate(fs):
                if arms_j[j] is None or arms_j[j][0] == 'skip':
                    per.append([])
                    continue
                sj = C.condSt(mx, j, st.cd, st)
                w = pas.under(('arm', x, j), lambda: self.ab_arm(sj, ma, g, rets, (q, K, ((), 0), ((), j + d))))
                if w is None:
                    break
                per.append(w)
            else:
                abs_.append((q, K, d))
                abw.append(per)
                self.stats['ab'] += 1
        ws = [('vp', vps[t][0], list(vps[t][1])) for t in keep] + [('ab',) + a for a in abs_]
        for j, a in enumerate(arms):
            if a[0] == 'skip':
                ws.append(a)
            else:
                ws += a[0]
                for t in keep:
                    ws += a[1][t]
                for per in abw:
                    ws += per[armj[j]]
        self.stats['vp'] += len(keep)
        assert len(self.H.calls) == st.nc
        self.H.calls.append(ws if ok else [('fail',)])
        return ws if ok else None

    def ab_arm(self, st, ma, g, rets, Q):
        """A block's run in the arm's state with the callee's guarantees pushed (`abArm`)."""
        G = self.X.sigOf(g)
        mr = C.setRM(C.monos(st.env, rets), C.instRM(ma, G.retM))
        S = st.copy()
        if not C.pushPost(G, ma + mr, S):
            return None
        return self.run(S, Q)

    def vp_arm(self, st, ma, g, rets, vps):
        """Per returned pointer, its cells' witnesses in the arm's state with the callee's guarantees pushed."""
        if not vps:
            return []
        G = self.X.sigOf(g)
        mr = C.setRM(C.monos(st.env, rets), C.instRM(ma, G.retM))
        S = st.copy()
        if not C.pushPost(G, ma + mr, S):
            return [None] * len(vps)
        out = []
        for j, offs in vps:
            m = C.nth(mr, j)
            w = [self.pt(S, C.cshift(m, o)) for o in offs] if m is not None else [None]
            out.append(None if None in w else w)
        return out

    def bit(self, pas, st, c, key):
        """A `log2Ceil` heap bit's witness (keyed as a read of the hint's destination)."""
        if key in self.H.reads:
            return self.H.reads[key]
        w = self.pt(st, c)
        if w is None:
            self.miss.append(('bit', key, c))
        self.H.reads[key] = w if w is not None else ('fail',)
        return w

    def eq(self, pas, st, a):
        """The atom's equation listed (`HCert.eqs`) when it says something the monomials do not: a `mul` whose
        product has a monomial and a factor none of its own, an `assertEq`/`copy` of two values with different
        ones."""
        k = a[0]
        if k == 'mul':
            d, x, y = a[1:]
            self.div(pas, st, d, x, y)
            if d in st.env and (x not in st.env or y not in st.env) and x not in self.X.dv and y not in self.X.dv:
                self.add_eq(d)
        elif k in ('assertEq', 'copy'):
            x, y = a[1], a[2]
            if x in st.env and y in st.env and st.env[x] != st.env[y]:
                self.add_eq(x)

    def add_eq(self, v):
        if v not in self.X.eqk:
            self.X.eqk.add(v)
            self.H.eqs.append(v)
            self.stats['eqs'] += 1

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
        for c, q in G.postQ:
            # the store of the cell (`word n`), then the run at its word
            t, tq = C.instC(ms, c), C.instR(ms, q)
            ns = [n for n, p in st.sv.items() if t is not None and p[0] == t]
            w = None
            if ns and tq is not None:
                m = st.sv[ns[-1]][1]
                w = self.run(st, (C.cmul(m, tq[0]), tq[1], tq[2], tq[3]))
            if w is None:
                self.miss.append(('ret', 'postQ', t, tq))
                return self.ret_done(None)
            ws += [('word', ns[-1])] + w
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
            if w is None and ex and C.noSlot0R(r):
                # at the exit's slots by `runOk` (several witnesses)
                q = C.instR(mx, r)
                wl = self.run(st, q) if q is not None else None
                if wl is not None:
                    ws += wl
                    continue
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
    H.fas = C.fa_pairs(body)
    H.dups = sorted(getattr(P, 'dups', ()))
    S = Solver(k, P, H, sigs)
    S.miss = []
    X_ = C.X(dict(I.POWS), H, sigOf, params, S)
    S.X = X_
    # `heapc.heapOkC` builds its own `X`: run the pass on ours
    pas = run_pass(X_, params, body)
    compact(H)
    return H, S, pas


def wit_res(w, f):
    """The witness with its residual indices mapped by `f`."""
    k = w[0]
    if k in ('run', 'pfr'):
        return (k, w[1], [f(i) for i in w[2]])
    if k == 'skip':
        return (k, [f(i) for i in w[1]])
    if k == 'mrg':
        return (k, w[1], [f(i) for i in w[2]])
    if k == 'mrgE':
        return (k, w[1], w[2], [f(i) for i in w[3]])
    if k == 'catM':
        return (k, w[1], w[2], [f(i) for i in w[3]])
    if k == 'perm':
        return (k, f(w[1]), w[2])
    if k in ('prep', 'app'):
        return (k, w[1], wit_res(w[2], f), [f(i) for i in w[3]])
    return w


def compact(H):
    """Only the residuals a witness lists, renumbered (the solver states some for candidates it does not take)."""
    used = set()

    def see(i):
        used.add(i)
        return i
    for w in list(H.reads.values()) + [w for ws in H.calls + H.rets for w in ws]:
        wit_res(w, see)
    new = {i: n for n, i in enumerate(sorted(used))}
    H.res = [H.res[i] for i in sorted(used)]
    H.reads = {k: wit_res(w, new.__getitem__) for k, w in H.reads.items()}
    H.calls = [[wit_res(w, new.__getitem__) for w in ws] for ws in H.calls]
    H.rets = [[wit_res(w, new.__getitem__) for w in ws] for ws in H.rets]


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
        P.block(C.dupB(X_.H.dups, body) if X_.H.dups else body, st)
    elif len(G.term) == 1 and G.term[0][0] == ('val', 0) and (G.term[0][1] == ('val', 1) or G.term[0][1][0] == 'num'):
        if G.retM or G.postV or G.postQ:
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
    if r[0] == 'subP':
        return f'.subP {lcell(r[1])} [{", ".join(map(lcell, r[2]))}]'
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
    if k == 'perm':
        return f'.perm {w[1]} {lnums(w[2])}'
    if k in ('prep', 'app'):
        return f'.{k} {w[1]} ({lwit(w[2])}) {lnums(w[3])}'
    if k == 'keep':
        return f'.keep {w[1]} {lcell(w[2])} {lcell(w[3])} {lcell(w[4])}'
    if k == 'vp':
        return f'.vp {w[1]} {lnums(w[2])}'
    if k == 'mrgE':
        return f'.mrgE {w[1]} {lcell(w[2])} {lnums(w[3])}'
    if k == 'catM':
        return f'.catM {lcell(w[1])} {lcell(w[2])} {lnums(w[3])}'
    if k == 'ab':
        return f'.ab {lcell(w[1])} {w[2]} {w[3]}'
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
    if G.postQ:
        fs.append('postQ := ' + ax.lst('sig_postQ', '(CoreMode.CCell × CoreMode.CRun)',
                                      (f'({lcell(c)}, {lrun(r)})' for c, r in G.postQ), '        '))
    if G.ghosts:
        fs.append(f'ghosts := {G.ghosts}')
    if G.retEq:
        fs.append('retEq := [' + ', '.join(f'({lcell(a)}, {lcell(b)})' for a, b in G.retEq) + ']')
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
    if H.eqs:
        out += f'  eqs := {lnums(sorted(H.eqs))}\n'
    if H.fas:
        out += '  fas := [' + wrap(f'({a}, {b})' for a, b in H.fas) + ']\n'
    if H.ders:
        out += '  ders := [' + wrap(map(lcell, H.ders)) + ']\n'
    if H.dups:
        out += '  dups := [' + ', '.join(map(str, H.dups)) + ']\n'
    if H.hvs:
        out += '  hvs := ' + ax.lst('hvs', 'ℕ', map(str, sorted(H.hvs))) + '\n'
    if H.gargs:
        out += '  gargs := [' + wrap((f'("{g}", {lnums(a)}, [{", ".join(map(lcell, ms))}])' for g, a, ms in H.gargs)) + ']\n'
    return ax.defs, out


def sig_text(arms):
    """The callees' signatures as a `match` on the name, its arms packed several to a line."""
    if not arms:
        return '(fun _ ↦ .empty)'
    return '(fun g ↦ match g with\n    ' + wrap(arms + ['| _ => .empty)'], '    ', 118).replace(',\n', '\n').replace(', |', ' |')


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
    built = build(res, only)
    sigs, certs, why, drops, stmt_names, stats = built
    passing = {k for k in certs if k not in why}
    import heapwin
    sigOf = lambda g: sigs.get(I.callee(g), C.EMPTY)
    # a certificate whose context alone (its tries, built in every window) is over a window's budget cannot be checked
    # in windows: passing the Python check, no kernel check (`nokernel`)
    nokernel = {k for k in passing if heapwin.W_CERT * heapwin.cert_size(certs[k]) > heapwin.BUDGET / 2}
    wins = sorted(k for k in passing - nokernel
                  if k in KERNEL_WIN or heapwin.fn_cost(k, certs[k], sigOf) > heapwin.BUDGET)
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
        oks = [k for k in ks if k in passing and k not in wins and k not in nokernel]
        cal = lambda k: sorted({I.callee(n) for n in stmt_names[k]} & set(I.CORE))
        imps = sorted({f'LeanVM.Guest.Pack.«{pack}».{po[k][1]}' for k in oks} |
                      {f'LeanVM.Guest.CoreMode.GenC.«{po[c][0]}».Data' for k in oks for c in cal(k)})
        ok = HEADER.format(pack=pack, mod='Ok', what=f'The kernel\'s heap checks of {len(oks)} functions.')
        ok += 'public import LeanVM.Guest.CoreMode.HeapC\npublic import LeanVM.Guest.Data.Pows\n'
        ok += ''.join(f'public import {m}\n' for m in imps)
        ok += f'public import LeanVM.Guest.CoreMode.GenC.«{pack}».Data\n\nset_option Elab.async false\n'
        for k in ks:
            aux, body = lcert(certs[k], sig_only=k not in passing or k in nokernel)
            auxt = ''.join(f'/-- Part of `hcert`. -/\n{d}\n' for d in aux)
            data += (f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n{auxt}'
                     f'/-- `{k}`: its heap certificate{"" if k in passing and k not in nokernel else " (its signature only: not checked)"}. -/\n'
                     f'def hcert : CoreMode.HCert where\n{body}\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        for k in oks:
            names = sorted(stmt_names[k])
            arms = [f'| "{n}" => Fn.«{I.callee(n)}».hcert.sig' for n in names if I.callee(n) in I.CORE]
            sig = sig_text(arms)
            ok += (f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n'
                   f'/-- `{k}`: the heap check. -/\n'
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
    # the windowed kernel checks (`heapwin.py`, `GenCW/<fn>/`)
    if wins and not only:
        wout = os.path.join(os.path.dirname(out), 'GenCW')
        wmods, wstale = heapwin.run(res, built, wins, wout, check=check_only)
        mods += wmods
        stale += wstale
        want = {os.path.join(wout, m.split('«')[1].split('»')[0], m.rsplit('.', 1)[1] + '.lean') for m in wmods}
        have = set(glob.glob(os.path.join(wout, '*', '*.lean')))
        if check_only:
            stale += sorted(have - want)
        else:
            for p in have - want:
                os.remove(p)
            for d in glob.glob(os.path.join(wout, '*')):
                if os.path.isdir(d) and not os.listdir(d):
                    os.rmdir(d)
    clean, inf_closed = I.closure(res)
    cw = collections.Counter(cause(k, why[k], res[k]) for k in why)
    print(f'certificates: {len(certs)}; the Python check passes {len(passing)} (closed, callees too: {len(closed)}); '
          f'the inference closes {len(inf_closed)}, of which pass {len(passing & inf_closed)}; '
          f'{len(packs)} packs, {lines} lines')
    print('  failures by first cause:', dict(cw.most_common()))
    print(f'  passing, no kernel check (certificate over half a window): {sorted(nokernel)}')
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
