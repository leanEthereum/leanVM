"""The witnesses of the carried facts' checks (`Res.carryGW`, `Res.carryNzW`, `CoreMode/Fam/CarryWit.lean`): for each
function, the events of its spine that the derivations of its searches use, as a bitset over the spine. The searches
(`Res.kOf`, `Res.ptrOk`, `Res.nzOf`, `Res.kIn`, `Res.tabNz`, `Res.selTabB`) are mirrored here returning the indices
of the events a success uses; the kernel runs the same searches over those events alone. Used by `carry.py`."""
import re

NZ_DEPTH, K_DEPTH = 12, 8


def enc(s):
    """`encS`: the name's bytes as digits in base `2^9`, each shifted by one, the first the lowest."""
    n = 0
    for c in reversed(s.encode()):
        n = n * 512 + c + 1
    return n


def ntree(items, val, ind='  '):
    """A balanced `NTree` literal over sorted `(key, value)` items."""
    if not items:
        return '.leaf'
    m = len(items) // 2
    k, v = items[m]
    return '(.node %d %s\n%s%s\n%s%s)' % (k, val(v), ind, ntree(items[:m], val, ind + ' '), ind,
                                         ntree(items[m + 1:], val, ind + ' '))


def tab(entries, val):
    """An `NTab` literal of `(name, payload)` entries: the payloads by the name's code."""
    by = {}
    for f, p in entries:
        ps = by.setdefault(enc(f), [])
        if p not in ps:
            ps.append(p)
    return ntree(sorted(by.items()), lambda ps: '[%s]' % ', '.join(map(val, ps)))


def hexbits(sub):
    """A bitset literal: bit `j` set for each `j` of `sub`."""
    return 'nat_hex%% "%x"' % sum(1 << j for j in sub)


def vals(a):
    return [x for x in a[1:] if isinstance(x, int)]


# ---- over events (`Memory.spineE`, in the check's view `carry.view`) ------------------------------------------------

class EvWit:
    """`nzOf kv sp`, `kIn kv sp` over a spine of events: each success's event indices, or `None`."""

    def __init__(self, sp, kv, upf, pows):
        self.sp, self.kv, self.upf, self.pows = sp, set(kv), upf, pows
        self.by = {}
        for j, e in enumerate(sp):
            for x in (vals(e[1]) if e[0] == 'a' else e[2]):
                self.by.setdefault(x, []).append(j)
        self.mk, self.mn = {}, {}

    def evs(self, v):
        return [(j, self.sp[j]) for j in sorted(set(self.by.get(v, ())))]

    def atoms(self, v, *kinds):
        return [(j, e[1]) for j, e in self.evs(v) if e[0] == 'a' and e[1][0] in kinds]

    def pin_in(self, v):
        for j, a in self.atoms(v, 'mul', 'load', 'touch', 'rangeCheck', 'assertInK', 'frameAddr', 'const'):
            if (a[0] == 'mul' and a[1] == a[2] == a[3] == v) or (a[0] in ('load', 'touch') and a[2] == v) or \
                    (a[0] in ('rangeCheck', 'assertInK') and v in a[1:3]) or (a[0] == 'frameAddr' and a[1] == v) or \
                    (a[0] == 'const' and a[1] == v and a[2] is not None and a[2][1] == 0):
                return {j}
        return None

    def k0(self, v):
        return set() if v in self.kv else self.pin_in(v)

    def k1(self, v):
        r = self.k0(v)
        if r is not None:
            return r
        for j, a in self.atoms(v, 'mul', 'add'):
            if a[1] == v:
                x, y = self.k0(a[2]), self.k0(a[3])
                if x is not None and y is not None:
                    return {j} | x | y
        return None

    def kin(self, n, v):
        key = (n, v)
        if key not in self.mk:
            r = self.k0(v)
            if r is None and n > 0:
                for j, a in self.atoms(v, 'mul', 'add'):
                    if a[1] != v:
                        continue
                    f = (lambda u: self.kin(n - 1, u)) if a[0] == 'mul' else self.k1
                    x = f(a[2])
                    y = f(a[3]) if x is not None else None
                    if y is not None:
                        r = {j} | x | y
                        break
            self.mk[key] = r
        return self.mk[key]

    def pin_nz(self, v):
        for j, e in self.evs(v):
            if e[0] == 'c':
                if any(w == v and self.upf(e[1], i) for i, w in enumerate(e[2])):
                    return {j}
                continue
            a = e[1]
            if (a[0] == 'const' and a[1] == v and a[2] is not None and a[2][1] == 0 and a[2][0] != 0) or \
                    (a[0] in ('load', 'touch') and a[2] == v) or (a[0] == 'rangeCheck' and v in a[1:3]):
                return {j}
        return None

    def nz(self, n, v):
        key = (n, v)
        if key not in self.mn:
            r = set() if v in self.kv else self.pin_nz(v)
            if r is None and n > 0:
                for j, a in self.atoms(v, 'mul', 'copy', 'assertEq', 'load'):
                    c = None
                    if a[0] == 'mul':
                        d, x, y = a[1:]
                        for ok, f in ((d == v, lambda: (self.nz(n - 1, x), self.nz(n - 1, y))),
                                      (y == v, lambda: (self.kin(K_DEPTH, x), self.nz(n - 1, d))),
                                      (x == v, lambda: (self.kin(K_DEPTH, y), self.nz(n - 1, d)))):
                            if ok:
                                p, q = f()
                                if p is not None and q is not None:
                                    c = p | q
                                    break
                    elif a[0] in ('copy', 'assertEq'):
                        d, s = a[1:]
                        for ok, u in ((d == v, s), (s == v, d)):
                            if ok:
                                c = self.nz(n - 1, u)
                                if c is not None:
                                    break
                    elif a[1] == v:
                        c = self.tab_nz(n - 1, a[2], a[3])
                    if c is not None:
                        r = {j} | c
                        break
            self.mn[key] = r
        return self.mn[key]

    def tab_nz(self, n, p, off):
        for j, a in self.atoms(p, 'mul'):
            if a[1] == p:
                for T, J in ((a[2], a[3]), (a[3], a[2])):
                    r = self.tab_at(n, T, J, off)
                    if r is not None:
                        return {j} | r
        return None

    def loads(self, T, o, nz):
        """A load of a value `w` at `T·g^o` with `nz(w)`: its events."""
        for l, x in self.atoms(T, 'load'):
            if x[2] == T and x[3] == o:
                q = nz(x[1])
                if q is not None:
                    return {l} | q
        return None

    def table(self, T, off, m, nz, acc):
        """Loads at each `T·g^(t + off)`, `t < m`, of values `nz` pins, with `acc`."""
        for t in range(m):
            hit = self.loads(T, t + off, nz)
            if hit is None:
                return None
            acc = acc | hit
        return acc

    def tab_at(self, n, T, J, off):
        for j, a in self.atoms(J, 'rangeCheck'):
            if a[1] != J:
                continue
            k = a[5]
            for i, c in self.atoms(k, 'const'):
                w = c[2]
                m = self.pows.get(w[0]) if c[1] == k and w is not None and w[1] == 0 else None
                if m is not None and m < 2 ** 28:
                    r = self.table(T, off, m + 1, lambda u: self.nz(n, u), {j, i})
                    if r is not None:
                        return r
        return None

    def sel_tab(self, sels, v):
        """`Res.selTabS sp sels v`, nothing listed: a load of `v` at `p·g^off`, `p = T·J`, `J` a selector of `m` arms,
        the spine storing at each `T·g^(t + off)`, `t < m`, a value it pins nonzero."""
        for j, a in self.atoms(v, 'load'):
            if a[1] != v:
                continue
            p, off = a[2], a[3]
            for i, b in self.atoms(p, 'mul'):
                if b[1] != p:
                    continue
                for T, J in ((b[2], b[3]), (b[3], b[2])):
                    for x, m in sels:
                        if x == J:
                            r = self.table(T, off, m, lambda u: self.nz(NZ_DEPTH, u), {j, i})
                            if r is not None:
                                return r
        return None


# ---- over atoms (`Bridge.spine`, in the raw core IR) ----------------------------------------------------------------

def heap_dest(a):
    """`atomHeapDest?`: a hint's heap destination `(p, off, len)`."""
    if a[0] == 'hint' and a[1][0] in ('witness', 'bits', 'bitsExp', 'digitsExp', 'windowsExp'):
        d = a[1][-1]
        if d[0] == 'heap':
            return tuple(d[1:])
    return None


class AtomWit:
    """`kOf kv sp`, `ptrOk sp` over a spine of atoms: each success's atom indices, or `None`."""

    def __init__(self, sp):
        self.sp = sp
        self.mk = {}

    def first(self, ok):
        return next(({j} for j, a in enumerate(self.sp) if ok(a)), None)

    def pin_k(self, v):
        return self.first(lambda a: (a[0] == 'hint' and a[1][0] in ('alloc', 'allocDyn') and a[1][1] == v) or
                          (a[0] in ('load', 'touch') and a[2] == v) or (a[0] == 'rangeCheck' and v in a[1:3]) or
                          (a[0] == 'frameAddr' and a[1] == v))

    def kof(self, kv, n, v):
        key = (tuple(kv), n, v)
        if key not in self.mk:
            r = set() if v in kv else self.pin_k(v)
            if r is None and n > 0:
                for j, a in enumerate(self.sp):
                    if a[0] == 'mul' and a[1] == v:
                        x = self.kof(kv, n - 1, a[2])
                        y = self.kof(kv, n - 1, a[3]) if x is not None else None
                        if y is not None:
                            r = {j} | x | y
                            break
            self.mk[key] = r
        return self.mk[key]

    def ptr(self, p):
        """`ptrOk sp p`."""
        x = self.first(lambda a: a[0] == 'hint' and a[1][0] in ('alloc', 'allocDyn') and a[1][1] == p) or \
            self.first(lambda a: a[0] == 'load' and a[2] == p)
        y = self.first(lambda a: a[0] == 'load' and a[2] == p and a[3] == 0) or \
            self.first(lambda a: (lambda d: d is not None and d[0] == p and d[1] == 0 and d[2] > 0)(heap_dest(a)))
        return x | y if x is not None and y is not None else None


def atom_spine(body, noret):
    """`Bridge.spine` over the raw core IR: the top-level atoms before the first statement that may return."""
    out = []
    for s in body:
        if s[0] == 'a':
            out.append(s[1])
        elif s[0] in ('call', 'callIf', 'dispatch'):
            pass
        elif s[0] in ('ite', 'match') and noret(s):
            pass
        else:
            break
    return out


def raw_atoms(body):
    """Every atom of a raw body, at any depth."""
    for s in body:
        if s[0] == 'a':
            yield s[1]
        elif s[0] == 'ite':
            yield from raw_atoms(s[2])
            yield from raw_atoms(s[3])
        elif s[0] == 'match':
            for x in s[2]:
                yield from raw_atoms(x)


def lean_carried(path):
    """`Res.carried` (`Fam/CarryDefs.lean`): `(stable name, parameter, kind)`."""
    t = open(path, encoding='utf-8').read()
    t = t[t.index('def carried :'):]
    t = t[:t.index('\n\n')]
    return [(f, int(p), k) for f, p, k in re.findall(r'name% «([^»]+)», (\d+), \.(\w+)\)', t)]


def name_strings(path):
    """The core functions' names by stable name (`Data/NameStrings.lean`)."""
    t = open(path, encoding='utf-8').read()
    return dict(re.findall(r'abbrev «([^»]+)» : String := "([^"]*)"', t))
