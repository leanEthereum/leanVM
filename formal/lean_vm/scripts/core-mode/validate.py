"""The core inference's residuals (`infer.py`, everything on) evaluated on honest executions: a regression check of the
residuals' truth, not a proof. Each residual is a statement on core names of one function instance (the values' words
and the ghost slots); this evaluates it at every instance of the function in real runs.

Runs come from the stable executor's `DBG_JUMP_DUMP=PATH` (every taken jump `(pc, fp, pc', fp')`, the final memory and
its written cells, as `PATH.<cycles>.{jumps,mem,written}`). The guest-export cases give leaves and nodes with
leanXMSS, leanSPHINCS and blobs (`exec_bench` adds a 900-signature leaf and a node over two):

  cd formal/lean_vm && LEANVM_DIR=$PWD/../.. LEANVM_EXEC_BENCH=1 DBG_JUMP_DUMP=/tmp/v/run LEANVM_GUEST_DIFF=/tmp/v/diff \\
    cargo test --release --manifest-path scripts/guest-export/Cargo.toml --lib guest_diff -- --ignored
  python3 -I scripts/core-mode/validate.py /tmp/v/run.* [--fn NAME] [--all] [--verbose]

An instance is a jump to a function's entry (`main` at frame 0); a value's word is its frame cell `fp + Cert.locs[v]`;
an exponent is the word's discrete log to `g = x`. A ghost slot's word is the parent's ghost instantiation at the call
site whose arguments are the child's parameters (the call sites `infer.py` records; a loop's next iteration is its
tail's). A residual is checked where the branch conditions it was asked under hold (`Pass.rpath`); one false there is
a false residual (exit status 1). One false only where none of its paths holds is reported apart: the Lean side states
residuals per instance, so it must still be true there, or be stated under its path. `--all` checks every residual,
not only those the witnesses use.
"""
import sys, os, collections, glob
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
argv = list(sys.argv)
sys.argv = sys.argv[:1]
import numpy as np
import infer as I
sys.modules.setdefault('infer', I)

ORD = 2 ** 64 - 1
POLY = (1 << 64) | 0x1b
GB = I.GB


# ---- K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1) and discrete logs to g = x

def kmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> 64:
            a ^= POLY
    return r


def kpow(a, e):
    r = 1
    while e:
        if e & 1:
            r = kmul(r, a)
        a = kmul(a, a)
        e >>= 1
    return r


PRIMES = (3, 5, 17, 257, 641, 65537, 6700417)


class DLog:
    """`x^i -> i`: a table below `2^N`, Pohlig-Hellman above (cached)."""

    def __init__(self, n=22):
        t = {}
        v = 1
        for i in range(1 << n):
            t[v] = i
            v <<= 1
            if v >> 64:
                v ^= POLY
        self.t, self.cache, self.bs = t, {}, {}

    def __call__(self, w):
        if w == 0:
            return None
        i = self.t.get(w)
        if i is not None:
            return i
        if w in self.cache:
            return self.cache[w]
        rs = []
        for p in PRIMES:
            e = ORD // p
            gp, hp = kpow(2, e), kpow(w, e)
            m = int(p ** 0.5) + 1
            if p not in self.bs:
                tb, v = {}, 1
                for j in range(m):
                    tb.setdefault(v, j)
                    v = kmul(v, gp)
                self.bs[p] = (tb, kpow(kpow(gp, m), ORD - 1))
            tb, step = self.bs[p]
            y, k = hp, None
            for i in range(m + 1):
                if y in tb:
                    k = (i * m + tb[y]) % p
                    break
                y = kmul(y, step)
            if k is None:
                self.cache[w] = None
                return None
            rs.append(k)
        x = 0
        for p, k in zip(PRIMES, rs):
            q = ORD // p
            x = (x + k * q * pow(q, -1, p)) % ORD
        self.cache[w] = x
        return x


# ---- a run's instances and valuations

class Run:
    def __init__(self, prefix, D, dl):
        self.name = os.path.basename(prefix)
        self.mem = np.fromfile(prefix + '.mem', dtype=np.uint64).reshape(-1, 2)
        self.wr = np.fromfile(prefix + '.written', dtype=np.uint8)
        j = np.fromfile(prefix + '.jumps', dtype=np.uint32).reshape(-1, 4)
        ent = {int(c['entry']): k for k, c in D['comp'].items()}
        self.inst = [('main', 0, None)]      # (function, fp, parent fp)
        seen = {0}
        for pc0, fp0, pc, fp in j.tolist():
            k = ent.get(pc)
            if k is not None and fp not in seen:
                seen.add(fp)
                self.inst.append((k, fp, fp0))
        self.byfp = {fp: n for n, (_, fp, _) in enumerate(self.inst)}
        self.dl = dl

    def word(self, cell):
        if cell >= len(self.wr) or not self.wr[cell]:
            return None
        w = self.mem[cell]
        return (int(w[0]), int(w[1]))

    def exp(self, w):
        if w is None or w[1] != 0:
            return None
        return self.dl(w[0])


class Inst:
    """One instance: its words by value number, exponents, ghost exponents."""

    def __init__(self, run, k, fp, locs):
        self.run, self.k, self.fp, self.locs = run, k, fp, locs
        self.ghosts = {}
        self._w, self._e = {}, {}

    def word(self, v):
        if v not in self._w:
            loc = self.locs[v] if v < len(self.locs) else None
            self._w[v] = self.run.word(self.fp + loc) if loc is not None and loc >= 2 else None
        return self._w[v]

    def exp(self, b):
        if b >= GB:
            return self.ghosts.get(b - GB)
        if b not in self._e:
            self._e[b] = self.run.exp(self.word(b))
        return self._e[b]

    def mono(self, m):
        """A monomial's exponent (modulo `g`'s order), `None` if a base has none."""
        s = m[1]
        for b, e in m[0]:
            x = self.exp(b)
            if x is None:
                return None
            s += e * x
        return s % ORD

    def path(self, p):
        """Whether the branch conditions `p` hold (`None`: unknown)."""
        for c in p:
            if c[0] == 'ite':
                w = self.word(c[1])
                if w is None:
                    return None
                if (w == (0, 0)) != c[2]:
                    return False
            else:
                x = self.exp(c[1])
                if x is None:
                    return None
                if x != c[2]:
                    return False
        return True


def signed(d):
    d %= ORD
    return d - ORD if d >= 2 ** 63 else d


def in_run(I_, x, R):
    """Exponent `x` is a cell of the run `R = (Q, S, lo, hi)`: `None` if unknown."""
    Q, S, lo, hi = R
    q, a, b = I_.mono(Q), I_.mono(lo), I_.mono(hi)
    if None in (q, a, b):
        return None
    d = signed(x - q)
    return d >= 0 and d % S == 0 and a <= d // S < b


def run_cells(I_, R, cap=1 << 16):
    Q, S, lo, hi = R
    q, a, b = I_.mono(Q), I_.mono(lo), I_.mono(hi)
    if None in (q, a, b) or b - a > cap:
        return None
    return [(q + S * j) % ORD for j in range(a, b)]


def in_parts(I_, x, parts):
    unk = False
    for p in parts:
        if len(p) == 4:
            r = in_run(I_, x, p)
        else:
            m = I_.mono(p)
            r = None if m is None else m == x
        if r:
            return True
        unk |= r is None
    return None if unk else False


def bases(x):
    """The value numbers (and ghost slots) a residual names."""
    if isinstance(x, tuple) and len(x) == 2 and isinstance(x[0], tuple) and all(
            isinstance(y, tuple) and len(y) == 2 and isinstance(y[0], int) for y in x[0]) and isinstance(x[1], int):
        return [b for b, _ in x[0]]
    if isinstance(x, (tuple, list)):
        return [b for y in x for b in bases(y)]
    return []


def holds(I_, r):
    """A residual's truth at the instance: True, False or None (a value without a word, a ghost unresolved)."""
    k = r[0]
    if k == 'lt':
        a, b = I_.mono(r[1]), I_.mono(r[2])
        return None if None in (a, b) else a < b
    if k == 'subR':
        if len(r[1]) == 4:                      # a run inside a run
            cells = run_cells(I_, r[1])
        else:                                   # `(bases, a, b)`: the cells `bases·g^j`, `a <= j < b`
            bs, a, b = r[1]
            base = I_.mono((bs, 0))
            cells = None if base is None else [(base + j) % ORD for j in range(a, b)]
        if cells is None:
            return None
        out = True
        for x in cells:
            t = in_run(I_, x, r[2])
            if t is None:
                return None
            out &= t
        return out
    if k == 'subP':                             # a cell among cells (`perm`)
        x = I_.mono(r[1])
        ps = [I_.mono(p) for p in r[2]]
        if x is None:
            return None
        if x in ps:
            return True
        return None if None in ps else False
    if k in ('sub', 'subPR'):
        if len(r[1]) == 2:                      # a cell inside a run (`narrow`)
            x = I_.mono(r[1])
            return None if x is None else in_run(I_, x, r[2])
        cells = run_cells(I_, r[1])
        if cells is None:
            return None
        parts = r[2]
        for x in cells:
            t = in_parts(I_, x, parts)
            if t is not True:
                return t
        return True
    return None


def check_loads(I_, body, out):
    """The frame map's check: every `load` on the instance's path reads its word at its address."""
    for s in body:
        if s[0] == 'a' and s[1][0] == 'load':
            _, d, p, off = s[1]
            e, w = I_.exp(p), I_.word(d)
            if e is None or w is None:
                out['unknown'] += 1
                continue
            o = 'ok' if I_.run.word((e + off) % ORD) == w else 'mismatch'
            out[o] += 1
            if o == 'mismatch':
                out['mismatch in ' + I_.k.split('__')[0]] += 1
        elif s[0] == 'ite':
            w = I_.word(s[1])
            if w is not None:
                check_loads(I_, s[2] if w == (0, 0) else s[3], out)
        elif s[0] == 'match':
            x = I_.exp(s[1])
            if x is not None and x < len(s[2]):
                check_loads(I_, s[2][x], out)


# ---- ghosts: the parent's call site

def site_ghosts(par, P, k, child):
    """The ghost exponents of `child` (an instance of `k`) from the parent's call sites to `k` whose arguments are the
    child's parameters; `None` if no site matches, `'ambiguous'` if matching sites disagree."""
    params = I.CORE[k][0]
    pw = [child.word(v) for v in params]
    found = set()
    for f, args, gi, path in P.sites:
        if f != k or len(args) != len(params):
            continue
        if any(par.word(a) != w for a, w in zip(args, pw)):
            continue
        if par.path(path) is False:
            continue
        found.add(tuple(None if m is None else par.mono(m) for m in (gi or ())))
    if not found:
        return None
    if len(found) > 1:
        return 'ambiguous'
    return dict(enumerate(found.pop()))


def main():
    files = [a for a in argv[1:] if not a.startswith('--')]
    fn = argv[argv.index('--fn') + 1] if '--fn' in argv else None
    files = [f for f in files if f != fn]
    prefixes = sorted({g.rsplit('.', 1)[0] for f in files for g in glob.glob(f) + glob.glob(f + '.jumps')
                       if g.endswith(('.jumps', '.mem', '.written'))})
    res, dt = I.run_all()
    print(f'inferred {len(res)} functions in {dt:.1f} s; runs: {len(prefixes)}')
    U = {k: (set(range(len(P.res))) if '--all' in argv else I.used_res(P)) for k, P in res.items()}
    D = I.D
    dl = DLog()
    stat = collections.Counter()
    per = collections.defaultdict(collections.Counter)      # (k, i) -> outcome counts
    ex = {}
    gh = collections.Counter()
    loads = collections.Counter()
    unknown = collections.Counter()
    for pre in prefixes:
        run = Run(pre, D, dl)
        insts = {}
        n_inst = collections.Counter()
        for n, (k, fp, pfp) in enumerate(run.inst):
            if k not in res:
                continue
            I_ = Inst(run, k, fp, D['comp'][k]['locs'])
            insts[fp] = I_
            n_inst[k] += 1
            P = res[k]
            if I.SIGS[k].ghosts and pfp is not None and pfp in insts:
                par = insts[pfp]
                g = site_ghosts(par, res[par.k], k, I_)
                gh['resolved' if isinstance(g, dict) else g or 'no site'] += 1
                if isinstance(g, dict):
                    I_.ghosts = {j: x for j, x in g.items() if x is not None}
            if '--loads' in argv:
                check_loads(I_, P.body, loads)
            if fn and k != fn:
                continue
            for i in sorted(U[k]):
                r = P.res[i]
                paths = P.rpath.get(i, [()])
                pv = [I_.path(p) for p in paths]
                on = True if any(v is True for v in pv) else (None if any(v is None for v in pv) else False)
                t = holds(I_, r)
                fam = I.res_family(P, r)
                key = ('true' if t else 'unknown' if t is None else 'FALSE') + \
                    ('' if on else ' (path unknown)' if on is None else ' (path not taken)')
                stat[(fam, key)] += 1
                per[(k, i)][key] += 1
                if t is None:
                    miss = sorted({b for b in bases(r) if I_.exp(b) is None})
                    why = 'ghost' if any(b >= GB for b in miss) else 'no word' if miss else 'too long'
                    unknown[(k.split('__')[0], why)] += 1
                if t is False:
                    bs = sorted({b for b in bases(r)})
                    ex.setdefault((k, i, key), (run.name, fp, {b: I_.exp(b) for b in bs}))
        print(f'{run.name}: {len(run.inst)} instances, {len(n_inst)} functions')
    print('ghosts:', dict(gh))
    if loads:
        print('loads (frame map check):', dict(loads))
    if unknown:
        print('not evaluated (function, why):', dict(unknown.most_common(12)))
    print('residual instances by family and outcome:')
    for (fam, key), n in sorted(stat.items()):
        print(f'  {fam[0]:9s} {fam[1]:14s} {key:28s} {n}')
    nres = len(per)
    false = {ki: c for ki, c in per.items() if any(o.startswith('FALSE') and 'path' not in o for o in c)}
    vac = {ki: c for ki, c in per.items() if ki not in false and any(o.startswith('FALSE') for o in c)}
    never = sum(1 for k, u in U.items() for i in u if (k, i) not in per)
    print(f'residuals evaluated: {nres} (not reached by any run: {never}); false where asked: {len(false)}; '
          f'false only off their paths: {len(vac)}')
    for title, d in (('FALSE', false), ('false off path', vac)):
        for (k, i), c in sorted(d.items()):
            r = res[k].res[i]
            w = [ex[(k, i, o)] for o in c if (k, i, o) in ex][:1]
            print(f'  {title}: {k} #{i} {I.res_family(res[k], r)} {dict(c)} at {w}: {str(r)[:300]}')
            if '--verbose' in argv:
                print('     paths', res[k].rpath.get(i))
    sys.exit(1 if false else 0)


if __name__ == '__main__':
    main()
