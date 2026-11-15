"""The witnesses of the `sub` families read off a function's own code (`Res.Wit`, `Res/FamDefs.lean`): for
each residual a family takes, the top-level atoms and selectors of the function's body its check reads,
mirroring `Res.shiftB`, `Res.sideB` and `Res.runB` (`cellLt`, `eqCells`, `mulBy`, `holdsBase`,
`sideRead`, `mulConst`). The kernel
checks the witness (`Res.witOk`) and the family on it, so a witness found here is only a hint.
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

    def lean(self):
        return '⟨[%s], [%s]⟩' % (', '.join(self.picked), ', '.join('(.n %d, %d)' % p for p in self.psels))


def witnesses(residuals):
    """Each function's witness text, for the functions whose `sub` residuals a family read off its code may
    take: `residuals` by stable name `{offset: [res]}` (`sel.residuals`)."""
    texts = None
    out = {}
    tabs = tab_params()
    for n, rs in residuals.items():
        subs = [r for l in rs.values() for r in l if r[0] == 'sub' and len(r[2]) == 1]
        if not subs:
            continue
        if texts is None:
            texts = bc.core_texts(); B = bc.bundles()
        if n not in texts or n not in B:
            continue
        f = Fn(n, texts[n], B[n]['locs'], set(tabs.get(n, ())))
        for r in subs:
            try:
                a, b = rng(r[1]), rng(r[2][0])
            except (ValueError, IndexError, TypeError):
                continue
            snap = (list(f.picked), list(f.psels))
            if not (f.shift(a, b) or f.side(a, b) or f.run(a, b)):
                f.picked, f.psels = snap
        if f.picked or f.psels:
            out[n] = f.lean()
    return out
