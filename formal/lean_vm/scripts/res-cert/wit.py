"""The witnesses of the `sub` families read off a function's own code (`Res.Wit`, `Res/FamDefs.lean`): for
each residual a family takes, the top-level atoms and selectors of the function's body its check reads,
mirroring `Res.shiftB`, `Res.sideB`, `Res.runB` (`cellLt`, `eqCells`, `mulBy`, `holdsBase`,
`sideRead`, `mulConst`), `Res.dimB` (`lowOk`), `Res.mulTileB`, `Res.extB` (`cellPow`, `mulCells`) and
`Res.expFamB` (`kVal`, `pw0`, `pw`, `eqX`, `mulX`, `Res/ExpDefs.lean`), and `Res.ordShiftB`'s bounds
(`idxPow`). The kernel
checks the witness (`Res.witOk`) and the family on it, so a witness found here is only a hint. The proof
stream's reads (`Res.stB`) need none.
"""
import os, sys, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('bcdata', os.path.join(HERE, '..', 'bridge-cert', 'data.py'))
bc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(bc)

# `Res.carried`'s exponent tables' bases: function -> parameter positions (`Res/CarryDefs.lean`)
CARRIED = os.path.join(bc.ROOT, 'Res', 'CarryDefs.lean')


def tab_params():
    import re
    t = open(CARRIED, encoding='utf-8').read()
    out = {}
    for m in re.finditer(r'\(name% «([^»]+)», (\d+), \.tab\)', t):
        out.setdefault(m.group(1), set()).add(int(m.group(2)))
    return out


# the functions of `Res.dimFacts` (`Res/TermDefs.lean`)
DIM_FNS = {'check_opening_terminal'}


# ---- the core IR, atoms kept whole ---------------------------------------------------------------------------

def pp(e):
    """A term back as Lean text."""
    if isinstance(e, int):
        return str(e)
    if e[0] == 'str':
        return '"%s"' % e[1]
    if e[0] == 'id':
        return e[1]
    if e[0] == 'app':
        return ' '.join([pp(e[1])] + [('(%s)' % pp(a)) if isinstance(a, tuple) and a[0] == 'app' else pp(a)
                                       for a in e[2]])
    if e[0] == 'list':
        return '[%s]' % ', '.join(pp(x) for x in e[1])
    if e[0] == 'tuple':
        return '(%s)' % ', '.join(pp(x) for x in e[1])
    raise ValueError(e)


def atom_of(e):
    """An atom as `(kind, values..., text)`, values by number."""
    h, a = bc.head(e)
    v = bc.val
    txt = pp(e)
    if h == '.const':
        return ('const', v(a[0]), txt)
    if h in ('.mul', '.add'):
        return (h[1:], v(a[0]), v(a[1]), v(a[2]), txt)
    if h == '.copy':
        return ('copy', v(a[0]), v(a[1]), txt)
    if h == '.load':
        return ('load', v(a[0]), v(a[1]), a[2], txt)
    if h == '.rangeCheck':
        return ('rangeCheck', v(a[0]), v(a[1]), v(a[2]), v(a[3]), v(a[4]), txt)
    if h == '.touch':
        return ('touch', v(a[0]), v(a[1]), txt)
    uses = []
    for x in a:
        try:
            uses.append(v(x))
        except Exception:
            pass
    return ('other', tuple(uses), txt)


def no_ret(e, env):
    h, a = bc.head(e)
    if h == '.ret':
        return False
    if h == '.ite':
        return all(no_ret(s, env) for s in bc.as_list(a[1], env)) and all(no_ret(s, env) for s in bc.as_list(a[2], env))
    if h == '.match_':
        return all(no_ret(s, env) for arm in bc.as_list(a[1], env) for s in bc.as_list(arm, env))
    return True


def top(text):
    """A body's top-level atoms (`Res.topAtoms`) and selectors (`Res.topSels`), as `(atoms, sels)`."""
    i = text.index('namespace core')
    ds = bc.defs(text[i:])
    cache = {}

    def env(n):
        if n not in cache:
            cache[n] = bc.parse(ds[n])
        return cache[n]
    atoms, sels, stop_a = [], [], False
    for s in bc.as_list(env('body'), env):
        h, a = bc.head(s)
        if h == '.match_':
            sels.append((bc.val(a[0]), len(bc.as_list(a[1], env))))
        elif h == '.dispatch':
            sels.append((bc.val(a[0]), len(bc.as_list(a[1], env))))
        if h == '.atom':
            if not stop_a:
                atoms.append(atom_of(a[0]))
            continue
        if not no_ret(s, env):
            break
    return atoms, sels


# ---- the residuals, structured ------------------------------------------------------------------------------

def num(x):
    return int(x)


def base(e):
    h, a = e[1][0], e[1][1:]
    if h == '.fr':
        return ('fr', num(a[0]))
    if h == '.hp':
        return ('hp', num(a[0]), num(a[1]))
    raise ValueError(e)


def mono(e):
    fp, k, bs = e[1]
    return (num(fp), num(k), [(base(x[1][0]), num(x[1][1])) for x in bs[1]])


def idx(e):
    h = e[1][0]
    if h == '.num':
        return ('num', num(e[1][1]))
    if h == '.ex':
        return ('ex', base(e[1][1]), num(e[1][2]))
    raise ValueError(e)


def rng(e):
    m, lo, hi, S, d = e[1]
    return (mono(m), idx(lo), idx(hi), num(S), num(d))


def blt(a, b):
    if a[0] == 'fr' and b[0] == 'fr':
        return a[1] < b[1]
    if a[0] == 'fr':
        return True
    if b[0] == 'fr':
        return False
    return (a[1], a[2]) < (b[1], b[2])


def insert_bs(be, bs):
    if not bs:
        return [be]
    b = bs[0]
    if be[0] == b[0]:
        return [(b[0], be[1] + b[1])] + bs[1:]
    if blt(be[0], b[0]):
        return [be] + bs
    return [b] + insert_bs(be, bs[1:])


_POWS = None


def pow_of(txt, one=False):
    """`Res.powOf` of a `const` atom's word, the guest's powers' (`Data.powTree`); with `one`, `Res.powOf1`,
    `1`'s exponent too."""
    global _POWS
    import re
    m = re.search(r'\(word (\d+) (\d+)\)\s*$', txt)
    if not m or int(m.group(2)) != 0:
        return None
    w = int(m.group(1))
    if one and w == 1:
        return 0
    if _POWS is None:
        sys.path.insert(0, os.path.join(HERE, '..', 'mode-cert'))
        import data
        _POWS = data.load()['pows']
    return _POWS.get(w)


def pow_of1(txt):
    return pow_of(txt, True)


# ---- the families' witnesses ---------------------------------------------------------------------------------

class Fn:
    def __init__(self, name, text, locs, tabs):
        self.atoms, self.sels = top(text)
        self.locs, self.tabs = locs, tabs
        self.picked, self.psels = [], []

    def cell(self, v):
        return self.locs[v] if v < len(self.locs) else 0

    def pick(self, a):
        if a[-1] not in self.picked:
            self.picked.append(a[-1])

    def const_of(self, k):
        for a in self.atoms:
            if a[0] == 'const' and a[1] == k:
                return a

    def rc_of(self, v):
        """A range check of value `v` and its bound's constant (`rcBound`)."""
        for a in self.atoms:
            if a[0] == 'rangeCheck' and a[1] == v:
                c = self.const_of(a[5])
                if c:
                    return [a, c]
        return None

    def cell_lt(self, o):
        """Every way `cellLt` can bound cell `o`: its range checks, its selectors."""
        got = False
        for a in self.atoms:
            if a[0] == 'rangeCheck' and self.cell(a[1]) == o:
                rc = self.rc_of(a[1])
                if rc:
                    for x in rc: self.pick(x)
                    got = True
        for (x, n) in self.sels:
            if self.cell(x) == o:
                use = next((a for a in self.atoms if x in a[1:-1]), None)
                if use is not None:
                    self.pick(use)
                if (x, n) not in self.psels:
                    self.psels.append((x, n))
                got = True
        return got

    def cell_pow(self, o):
        """`cellPow`: cell `o` bounded (`cellLt`), or touched."""
        if self.cell_lt(o):
            return True
        for a in self.atoms:
            if a[0] == 'touch' and self.cell(a[2]) == o:
                self.pick(a)
                return True
        return False

    def mul_tile(self, a, b, c):
        """`Res.mulTileB`: `[p] = [x]·[y]` a top-level product, `[x]` and `[y]` powers of `g`."""
        def fr(i):
            return i[1][1] if i[0] == 'ex' and i[1][0] == 'fr' and i[2] == 0 else None
        p, x, y = fr(a[2]), fr(b[2]), fr(c[2])
        if p is None or x is None or y is None:
            return False
        for m in self.atoms:
            if m[0] == 'mul' and self.cell(m[1]) == p and sorted((self.cell(m[2]), self.cell(m[3]))) == sorted((x, y)):
                if self.cell_pow(x) and self.cell_pow(y):
                    self.pick(m)
                    return True
        return False

    def ext(self, a):
        """`Res.extB`: the bound `[o] + 1`, `[o]` a power of `g`."""
        hi = a[2]
        return hi[0] == 'ex' and hi[1][0] == 'fr' and hi[2] == 1 and self.cell_pow(hi[1][1])

    def eq_cells(self, c):
        cs = [c]
        for a in self.atoms:
            if a[0] == 'copy' and (self.cell(a[1]) == c or self.cell(a[2]) == c):
                self.pick(a)
                cs.append(self.cell(a[2]) if self.cell(a[1]) == c else self.cell(a[1]))
        return cs

    def holds_base(self, o, B):
        if B[0] == 'fr':
            return B[1] == o
        for a in self.atoms:
            if a[0] == 'load' and self.cell(a[1]) == o and self.cell(a[2]) == B[1] and a[3] == B[2]:
                self.pick(a)
                return True
        return False

    def shift(self, a, b):
        if a[2][0] != 'ex' or a[2][1][0] != 'fr' or a[2][2] != 0:
            return False
        c = a[2][1][1]
        if not self.cell_lt(c):
            return False
        cs = self.eq_cells(c)
        for B, e in a[0][2]:
            if e != 1 or a[0][2] != insert_bs((B, 1), b[0][2]):
                continue
            for m in self.atoms:
                if m[0] != 'mul':
                    continue
                d, x, y = self.cell(m[1]), self.cell(m[2]), self.cell(m[3])
                for f, o in ((x, y), (y, x)):
                    if f not in cs or not self.holds_base(o, B) or not self.cell_lt(o):
                        continue
                    hi = b[2]
                    if hi[0] == 'ex' and hi[1] == ('fr', d) and hi[2] == 0:
                        self.pick(m); return True
                    if hi[0] == 'num' and self.cell_lt(d):
                        self.pick(m); return True
        return False

    def side(self, a, b):
        bs, bb = a[0][2], b[0][2]
        if len(bs) != 2 or len(bb) != 1 or bs[1][0][0] != 'hp' or bs[0][0][0] != 'fr':
            return False
        q, r = bs[1][0][1], bs[1][0][2]
        for ld in self.atoms:
            if ld[0] != 'load' or self.cell(ld[2]) != q or ld[3] != r:
                continue
            y = ld[1]
            rc = self.rc_of(y)
            if not rc:
                continue
            for m in self.atoms:
                if m[0] != 'mul' or m[3] != y or m[2] not in self.tabs:
                    continue
                for l2 in self.atoms:
                    if l2[0] == 'load' and l2[2] == m[1] and l2[3] == 212:
                        c = self.const_of(l2[1])
                        if c:
                            for z in [ld] + rc + [m, l2, c]: self.pick(z)
                            return True
        return False

    def run(self, a, b):
        if a[1][0] != 'num' or a[2][0] != 'num' or b[2][0] != 'ex' or b[2][1][0] != 'fr':
            return False
        p = b[2][1][1]
        for B, e in a[0][2]:
            if e != 1 or a[0][2] != insert_bs((B, 1), b[0][2]):
                continue
            for m in self.atoms:
                if m[0] != 'mul' or self.cell(m[1]) != p:
                    continue
                for f, c in ((m[2], m[3]), (m[3], m[2])):
                    k = self.const_of(c)
                    if k and self.holds_base(self.cell(f), B) and self.cell_lt(self.cell(f)):
                        self.pick(m); self.pick(k)
                        return True
        return False

    def dim(self, a, b):
        """`Res.lowOk`'s product: a frame cell a top-level product writes of a loaded value and a constant."""
        bs, bb = a[0][2], b[0][2]
        if len(bs) != 2 or len(bb) != 1 or bs[0] != bb[0] or bs[1][0][0] != 'fr':
            return False
        P = bs[1][0][1]
        for m in self.atoms:
            if m[0] != 'mul' or self.cell(m[1]) != P:
                continue
            k = self.const_of(m[3])
            ld = next((l for l in self.atoms if l[0] == 'load' and l[1] == m[2]), None)
            if k and ld:
                for z in (m, ld, k): self.pick(z)
                return True
        return False

    # ---- `Res.expFamB`: runs a product's factors bound ----

    def cell_lt_n(self, o, N):
        """`cellLt j w o N`, its bound checked."""
        for a in self.atoms:
            if a[0] == 'rangeCheck' and self.cell(a[1]) == o:
                c = self.const_of(a[5])
                if c:
                    z = pow_of(c[-1])
                    if z is not None and z + 1 <= N and z + 1 <= 2 ** 33:
                        self.pick(a); self.pick(c)
                        return True
        for (x, n) in self.sels:
            if self.cell(x) == o and n <= N:
                use = next((a for a in self.atoms if x in a[1:-1]), None)
                if use is not None:
                    self.pick(use)
                if (x, n) not in self.psels:
                    self.psels.append((x, n))
                return True
        return False

    def kval1(self, o):
        for a in self.atoms:
            if a[0] == 'const' and self.cell(a[1]) == o:
                z = pow_of1(a[-1])
                if z is not None:
                    self.pick(a)
                    return z
        return None

    def kval(self, o):
        z = self.kval1(o)
        if z is not None:
            return z
        for m in self.atoms:
            if m[0] == 'mul' and self.cell(m[1]) == o:
                zx, zy = self.kval1(self.cell(m[2])), self.kval1(self.cell(m[3]))
                if zx is not None and zy is not None:
                    self.pick(m)
                    return zx + zy
        return None

    def pw0(self, o):
        if self.cell_lt_n(o, 2 ** 39):
            return True
        z = self.kval(o)
        return z is not None and z < 2 ** 39

    def muls(self):
        return [(m, self.cell(m[1]), self.cell(m[2]), self.cell(m[3])) for m in self.atoms if m[0] == 'mul']

    def pw(self, o):
        if self.pw0(o):
            return True
        for a in self.atoms:
            if a[0] == 'copy':
                d, s_ = self.cell(a[1]), self.cell(a[2])
                if (d == o and self.pw0(s_)) or (s_ == o and self.pw0(d)):
                    self.pick(a)
                    return True
        for m, P, X, Y in self.muls():
            if P == o and self.pw0(X) and self.pw0(Y):
                self.pick(m)
                return True
            if X == o and self.pw0(Y):
                for m2, P2, X2, Y2 in self.muls():
                    if P2 == P and Y2 == Y and self.pw0(X2):
                        self.pick(m); self.pick(m2)
                        return True
        return False

    def eqx(self, a, b):
        if a == b:
            return True
        for at in self.atoms:
            if at[0] == 'copy':
                d, s_ = self.cell(at[1]), self.cell(at[2])
                if (d, s_) in ((a, b), (b, a)):
                    self.pick(at)
                    return True
        for m, P, X, Y in self.muls():
            if (P, X) in ((a, b), (b, a)) and self.kval(Y) == 0:
                self.pick(m)
                return True
        return False

    def mulx(self, okP, okU, okV):
        for m, P, X, Y in self.muls():
            if okP(P) and ((okU(X) and okV(Y)) or (okU(Y) and okV(X))):
                self.pick(m)
                return True
        return False

    def exp_hi(self, hi):
        if hi[0] == 'ex' and hi[1][0] == 'fr' and hi[2] == 0:
            return lambda P: self.eqx(P, hi[1][1])
        if hi[0] == 'num':
            return lambda P: self.cell_lt_n(P, hi[1] + 1)
        return None

    def exp_shift(self, a, b):
        if not (a[2][0] == 'ex' and a[2][1][0] == 'fr' and a[2][2] == 0):
            return False
        c = a[2][1][1]
        okP = self.exp_hi(b[2])
        if okP is None or a[1] != ('num', 0) or b[1] != ('num', 0) or a[3] != 1 or b[3] != 1 or a[4] != b[4] \
                or a[0][0] != b[0][0] or not self.pw(c):
            return False
        (_, k, bs), (_, bk, bbs) = a[0], b[0]
        if k == bk:
            for B, e in bs:
                if e == 1 and bs == insert_bs((B, 1), bbs) and \
                        self.mulx(okP, lambda u: self.eqx(u, c), lambda v: self.holds_base(v, B) and self.pw(v)):
                    return True
        if bs == bbs and bk <= k < bk + 2 ** 39:
            return self.mulx(okP, lambda u: self.eqx(u, c), lambda v: self.kval(v) == k - bk)
        return False

    def exp_fac(self, a, b):
        if a[2][0] != 'ex' or a[2][2] != 0 or b[2][0] != 'ex' or b[2][1][0] != 'fr' or b[2][2] != 0 or a[1][0] != 'num':
            return False
        X, p = a[2][1], b[2][1][1]
        if a[0] != b[0] or a[1] != b[1] or a[3] != b[3] or a[4] != b[4]:
            return False
        return self.mulx(lambda P: self.eqx(P, p), lambda u: self.holds_base(u, X) and self.pw(u), self.pw)

    def exp_pt(self, a, b):
        if b[2][0] != 'ex' or b[2][1][0] != 'fr' or b[2][2] < 1:
            return False
        p = b[2][1][1]
        if a[1] != ('num', 0) or a[2] != ('num', 1) or b[1] != ('num', 0) or b[3] != 1 or a[4] != b[4] \
                or a[0][0] != b[0][0] or a[0][1] != b[0][1]:
            return False
        for B, e in a[0][2]:
            if e == 1 and a[0][2] == insert_bs((B, 1), b[0][2]) and \
                    self.mulx(lambda P: self.eqx(P, p), lambda u: self.holds_base(u, B) and self.pw(u), self.pw):
                return True
        return False

    def ord_shift(self, a, b):
        """`Res.ordShiftB`'s shape, its exponents' frame cells bounded by `pw` where they are (`idxPow`; a
        selector's base needs no atom)."""
        def succ(i):
            return ('num', i[1] + 1) if i[0] == 'num' else ('ex', i[1], i[2] + 1)
        for x, y in ((a, b), (b, a)):
            if x[0] == y[0] and x[3] == y[3] and x[1] == succ(y[1]) and x[2] == succ(y[2]) and \
                    x[4] + x[3] == y[4] + 2 ** 64 - 1:
                for i in (y[1], y[2]):
                    if i[0] == 'ex' and i[1][0] == 'fr':
                        self.pw(i[1][1])
                return True
        return False

    def exp(self, a, b):
        return self.exp_shift(a, b) or self.exp_fac(a, b) or self.exp_pt(a, b)

    def lean(self):
        """The witness, its atoms in their order among the top-level atoms (`witOk` checks a sublist)."""
        pos = {}
        for k, a in enumerate(self.atoms):
            pos.setdefault(a[-1], k)
        picked = sorted(set(self.picked), key=lambda t: pos[t])
        return '⟨[%s], [%s]⟩' % (', '.join(picked), ', '.join('(.n %d, %d)' % p for p in self.psels))


def witnesses(residuals):
    """Each function's witness text, for the functions whose `sub` residuals a family read off its code may
    take: `residuals` by stable name `{offset: [res]}` (`sel.residuals`)."""
    texts = None
    out = {}
    tabs = tab_params()
    for n, rs in residuals.items():
        subs = [r for l in rs.values() for r in l if r[0] == 'sub' and len(r[2]) in (1, 2)]
        if not subs:
            continue
        if texts is None:
            texts = bc.core_texts(); B = bc.bundles()
        if n not in texts or n not in B:
            continue
        f = Fn(n, texts[n], B[n]['locs'], set(tabs.get(n, ())))
        for r in subs:
            try:
                rs2 = [rng(x) for x in r[2]]
                a = rng(r[1])
            except (ValueError, IndexError, TypeError):
                continue
            snap = (list(f.picked), list(f.psels))
            if len(rs2) == 2:
                ok = f.mul_tile(a, rs2[0], rs2[1]) or f.ext(a)
            else:
                b = rs2[0]
                ok = f.shift(a, b) or f.side(a, b) or f.run(a, b) or (n in DIM_FNS and f.dim(a, b)) or f.exp(a, b) or f.ord_shift(a, b)
            if not ok:
                f.picked, f.psels = snap
        if f.picked or f.psels:
            out[n] = f.lean()
    return out
