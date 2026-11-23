"""Writes `Guest/CoreMode/Gen/CarryNzList.lean`, `CarryCallers{k}.lean` and `CarryOk.lean`: the carried facts' check
(`Res.carryG`: every call site passes the listed callees' carried facts, every heap witness pointer its spine does not
pin is in `K` by the carried values) and the nonzero facts' check (`Res.carryNzG`: every call site passes its callees'
nonzero parameters, every dynamic allocation's size is nonzero in `K`, every listed callee word is) over the whole
program by ranges, and their conjunctions. The carried parameters of `carryG` are `Res.carried` (`CoreMode/Fam/CarryDefs.lean`);
those of `carryNzG` (`Res.carriedNz`), its callee words (`Res.nzUp`) and the values each body pins itself (`Res.ownNz`)
are derived here, by mirroring the check over the core IR (`Pack/*/Core*.lean`) to a fixed point, and written to
`CarryNzList.lean`. `--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/carry.py [--check]"""
import sys, os, glob, re

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resgen
import heapc
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402

from compiled import BD  # noqa: E402

OUT = resgen.OUT
# by ranges of functions, each a kernel check; `main` (function 0) alone
RANGES = [(0, 1), (1, 10), (11, 1), (12, 1), (13, 7), (20, 10), (30, 10), (40, 60), (100, 270), (370, 3), (373, 3), (376, 3), (379, 2), (381, 19), (400, 200), (600, 200), (800, 200), (1000, 200), (1200, None)]
# `Res.nzDepth`, `Res.kDepth`
NZ_DEPTH, K_DEPTH = 12, 8


# ---- the core IR, as `Res.carryNzG` reads it -------------------------------------------------------------------------

def atom(a):
    """An atom of the shared parse (`data.core_atom`) as the check reads it."""
    k = a[0]
    if k in ('const', 'mul', 'add', 'copy', 'touch', 'assertInK', 'assertEq', 'load', 'rangeCheck'):
        return a
    if k == 'frameAddr':
        return a[:2]
    if k == 'hint' and a[1][0] == 'allocDyn':
        return a[1]
    return ('other',)


def view(body):
    out = []
    for s in body:
        if s[0] == 'a':
            out.append(('atom', atom(s[1])))
        elif s[0] == 'ite':
            out.append(('ite', s[1], view(s[2]), view(s[3])))
        elif s[0] == 'match':
            out.append(('match', s[1], [view(x) for x in s[2]]))
        else:
            out.append(s)
    return out


def functions():
    """Each core function by name: its parameter count, loop flag (`Fn.loop`) and body."""
    F = {}
    for text in BD.core_texts().values():
        params, body, name = BD.core_fn(text)
        body = view(body)
        assert params == list(range(len(params))), name
        loop = len(body) >= 2 and body[-1] == ('ret', []) and body[-2][0] == 'callIf' and body[-2][2] == name
        F[name] = dict(np=len(params), loop=loop, body=body)
    return F


_POWS = []


def POWS():
    """The guest's powers of `g` (`Data.powTree`, `Res.powOf`), by word."""
    if not _POWS:
        import infer
        _POWS.append(dict(infer.D['pows']))
    return _POWS[0]


# ---- the check, mirrored -------------------------------------------------------------------------------------------

def no_ret(ss):
    return all(map(heapc.noret, ss))


def spine(ss):
    """`Memory.spineE`: the atoms and calls on every path through a block, as events."""
    out = []
    for s in ss:
        if s[0] == 'atom':
            out.append(('a', s[1]))
        elif s[0] == 'call':
            out.append(('c', s[1], s[2] + s[3]))
        elif s[0] in ('callIf', 'dispatch'):
            pass
        elif s[0] == 'ite' and no_ret(s[2]) and no_ret(s[3]):
            pass
        elif s[0] == 'match' and all(no_ret(x) for x in s[2]):
            pass
        else:
            break
    return out


def scoped(ss, ctx):
    """`Memory.allB`'s statements, each with its context."""
    for s in ss:
        yield s, ctx
        if s[0] == 'ite':
            yield from scoped(s[2], ctx + spine(s[2]))
            yield from scoped(s[3], ctx + spine(s[3]))
        elif s[0] == 'match':
            for x in s[2]:
                yield from scoped(x, ctx + spine(x))


class Check:
    def __init__(self, F, carried, upf):
        self.F, self.carried, self.upf = F, carried, upf
        self._tab_key = None
        self._kc = {}
        self._own = {}

    def _kidx(self, sp):
        """`sp`'s values put in `K` by one event (`pinIn`) and the products and sums defining each, computed once a
        context (the context kept, so its `id` is not reused)."""
        key = id(sp)
        hit = self._kc.get(key)
        if hit is None or hit[0] is not sp:
            pins, defs = set(), {}
            for e in sp:
                if e[0] != 'a':
                    continue
                a = e[1]
                if a[0] in ('load', 'touch'):
                    pins.add(a[2])
                elif a[0] in ('rangeCheck', 'assertInK'):
                    pins.update(a[1:3])
                elif a[0] == 'frameAddr':
                    pins.add(a[1])
                elif a[0] == 'const' and a[2] is not None and a[2][1] == 0:
                    pins.add(a[1])
                if a[0] == 'mul' and a[1] == a[2] == a[3]:
                    pins.add(a[1])
                if a[0] in ('mul', 'add'):
                    defs.setdefault(a[1], []).append((a[0], a[2], a[3]))
            hit = self._kc[key] = (sp, pins, defs, {})
        return hit

    def k_in(self, kv, sp, n, v):
        """`Res.kIn`: a listed value, one an event puts in `K` (`pinIn`, `v = v·v` among them), a product of such, `n`
        deep, or a sum of such one deep (`kIn1`)."""
        if v in kv:
            return True
        _, pins, defs, memo = self._kidx(sp)
        if v in pins:
            return True
        key = (tuple(kv), n, v)
        if key not in memo:
            memo[key] = n > 0 and any(
                (self.k_in(kv, sp, n - 1, x) and self.k_in(kv, sp, n - 1, y)) if op == 'mul' else
                (self.k_in1(kv, sp, x) and self.k_in1(kv, sp, y)) for op, x, y in defs.get(v, ()))
        return memo[key]

    def k_in1(self, kv, sp, v):
        """`Res.kIn1`: listed or put in `K` by an event (`kIn0`), or a product or sum of two such."""
        _, pins, defs, _ = self._kidx(sp)
        k0 = lambda u: u in kv or u in pins
        return k0(v) or any(k0(x) and k0(y) for _, x, y in defs.get(v, ()))

    def pin_nz(self, e, v):
        if e[0] == 'c':
            return any(w == v and self.upf(e[1], i) for i, w in enumerate(e[2]))
        a = e[1]
        return (a[0] == 'const' and a[1] == v and a[2] is not None and a[2][1] == 0 and a[2][0] != 0) or \
            (a[0] in ('load', 'touch') and a[2] == v) or (a[0] == 'rangeCheck' and v in a[1:3])

    def nz(self, kv, sp, n, v):
        if v in kv or any(self.pin_nz(e, v) for e in sp):
            return True
        if n == 0:
            return False
        for e in sp:
            if e[0] != 'a':
                continue
            a = e[1]
            if a[0] == 'mul':
                d, x, y = a[1:]
                if (d == v and self.nz(kv, sp, n - 1, x) and self.nz(kv, sp, n - 1, y)) or \
                        (y == v and self.k_in(kv, sp, K_DEPTH, x) and self.nz(kv, sp, n - 1, d)) or \
                        (x == v and self.k_in(kv, sp, K_DEPTH, y) and self.nz(kv, sp, n - 1, d)):
                    return True
            elif a[0] in ('copy', 'assertEq'):
                d, s = a[1:]
                if (d == v and self.nz(kv, sp, n - 1, s)) or (s == v and self.nz(kv, sp, n - 1, d)):
                    return True
            elif a[0] == 'load' and a[1] == v and self.tab_nz(kv, sp, n, a[2], a[3]):
                return True
        return False

    def tab_nz(self, kv, sp, n, p, off):
        """`Res.tabNz`: a read at `p·g^off`, `p = T·J`, `J` range checked against the constant `g^m`, of a table whose
        cells `T·g^(t + off)`, `t <= m`, the context stores values nonzero in `K`."""
        if self._tab_key is None or self._tab_key[0] is not sp:
            self._tab_key = (sp, [e[1] for e in sp if e[0] == 'a'])
        atoms = self._tab_key[1]
        for a in atoms:
            if a[0] != 'mul' or a[1] != p:
                continue
            for T, J in ((a[2], a[3]), (a[3], a[2])):
                for r in atoms:
                    if r[0] != 'rangeCheck' or r[1] != J:
                        continue
                    c = next((x[2] for x in atoms if x[0] == 'const' and x[1] == r[5]), None)
                    m = POWS().get(c[0]) if c is not None and c[1] == 0 else None
                    if m is not None and m < 2 ** 28 and all(
                            any(x[0] == 'load' and x[2] == T and x[3] == t + off and self.nz(kv, sp, n - 1, x[1])
                                for x in atoms) for t in range(m + 1)):
                        return True
        return False

    def own(self, f):
        """The values `f`'s body pins itself (`Res.ownNz`), computed once."""
        if f not in self._own:
            self._own[f] = self.arm_nz(self.F[f]['body']) + self.sel_tab(self.F[f]['body'])
        return self._own[f]

    def kv(self, f):
        """`Res.kvNz`."""
        return sorted(self.carried.get(f, ())) + ([0] if self.F[f]['loop'] else []) + self.own(f)

    def arm_nz(self, body):
        """The values `Res.armNzB` takes: copies in a top-level `match`'s first arm, before any return, that every arm
        pins nonzero on its own (its spine, nothing carried)."""
        out = []
        for s in body:
            if s[0] == 'match' and s[2]:
                sps = [spine(a) for a in s[2]]
                cands = [e[1][1] for e in sps[0] if e[0] == 'a' and e[1][0] == 'copy']
                out += [v for v in cands if all(self.nz([], sp, NZ_DEPTH, v) for sp in sps)]
            if not heapc.noret(s):
                break
        return out

    def sel_tab(self, body):
        """The values `Res.selTabB` takes: read by the body's spine at `T·J·g^off`, `J` a top-level `match`'s selector of
        `m` arms, the spine storing at each `T·g^(t + off)`, `t < m`, a value it pins nonzero."""
        sels = []
        for s in body:
            if s[0] == 'match':
                sels.append((s[1], len(s[2])))
            if not heapc.noret(s):
                break
        sp = spine(body)
        atoms = [e[1] for e in sp if e[0] == 'a']
        out = []
        for a in atoms:
            if a[0] != 'load':
                continue
            v, p, off = a[1], a[2], a[3]
            for b in atoms:
                if b[0] != 'mul' or b[1] != p:
                    continue
                if any(J == x and all(any(c[0] == 'load' and c[2] == T and c[3] == t + off and self.nz([], sp, NZ_DEPTH, c[1])
                                          for c in atoms) for t in range(m))
                       for T, J in ((b[2], b[3]), (b[3], b[2])) for x, m in sels):
                    out.append(v)
                    break
        return out

    def sites(self, f):
        """Each call site of `f`: its callee, arguments and context."""
        for s, ctx in scoped(self.F[f]['body'], spine(self.F[f]['body'])):
            if s[0] == 'call':
                yield s[1], s[2], ctx
            elif s[0] == 'callIf':
                yield s[2], s[3], ctx
            elif s[0] == 'dispatch':
                for g in s[2]:
                    yield g, s[3], ctx

    def dyns(self, f):
        for s, ctx in scoped(self.F[f]['body'], spine(self.F[f]['body'])):
            if s[0] == 'atom' and s[1][0] == 'allocDyn':
                yield s[1][2], ctx

    def up_ok(self, g, i):
        """`Res.upChk`."""
        G = self.F[g]
        if i < G['np']:
            return self.nz([], spine(G['body']), NZ_DEPTH, i)
        return all(i - G['np'] < len(s[1]) and self.nz([], ctx, NZ_DEPTH, s[1][i - G['np']])
                   for s, ctx in scoped(G['body'], spine(G['body'])) if s[0] == 'ret')

    def fails(self):
        out = []
        for f in self.F:
            kv = self.kv(f)
            for v, ctx in self.dyns(f):
                if not self.nz(kv, ctx, NZ_DEPTH, v):
                    out.append((f, 'size', v))
            for g, args, ctx in self.sites(f):
                for p in sorted(self.carried.get(g, ())):
                    if not (p < len(args) and self.nz(kv, ctx, NZ_DEPTH, args[p])):
                        out.append((f, 'site', g, p))
        return out


def nz_lists(F):
    """The carried parameters and callee words of `Res.carryNzG`: a fixed point of the mirrored check. A value it
    needs is pinned with the parameters of its function carried, the fewest of them; a callee word where the callee's
    own body pins it."""
    carried, memo = {}, {}

    def upf(g, i):
        if g not in F:
            return False
        if (g, i) not in memo:
            memo[(g, i)] = False
            memo[(g, i)] = C.up_ok(g, i)
        return memo[(g, i)]
    C = Check(F, carried, upf)

    def need(f, ctx, v):
        """Make `v` pinned in `f` at `ctx` by carried parameters, the fewest; whether it is."""
        if C.nz(C.kv(f), ctx, NZ_DEPTH, v):
            return
        old = set(carried.get(f, ()))
        carried[f] = old | set(range(F[f]['np']))
        if not C.nz(C.kv(f), ctx, NZ_DEPTH, v):
            carried[f] = old
            return
        for p in sorted(carried[f] - old):
            carried[f].discard(p)
            if not C.nz(C.kv(f), ctx, NZ_DEPTH, v):
                carried[f].add(p)
    callers = {}
    for f in F:
        for g, args, ctx in C.sites(f):
            callers.setdefault(g, []).append((f, args, ctx))
    for f in F:
        for v, ctx in C.dyns(f):
            need(f, ctx, v)
    done = False
    while not done:
        done = True
        for g in sorted(carried):
            for p in sorted(carried[g]):
                for f, args, ctx in callers.get(g, []):
                    before = sum(len(x) for x in carried.values())
                    if p < len(args):
                        need(f, ctx, args[p])
                    if sum(len(x) for x in carried.values()) != before:
                        done = False
    carried = {f: x for f, x in carried.items() if x}
    up = sorted(k for k, ok in memo.items() if ok)
    ups = set(up)
    C2 = Check(F, carried, lambda g, i: (g, i) in ups)
    bad = C2.fails() + [(g, 'up', i) for g, i in up if not C2.up_ok(g, i)]
    own = sorted((f, v) for f in F for v in set(C2.own(f)))
    return carried, up, own, bad


# ---- the modules ---------------------------------------------------------------------------------------------------

header = genfiles.header('core-mode/carry.py')


def render():
    files = {}
    F = functions()
    carried, up, own, bad = nz_lists(F)
    if bad:
        sys.exit('carry: the nonzero facts\' check fails:\n  ' + '\n  '.join(map(str, bad)))
    assert 'main' not in carried
    mod = 'LeanVM.Guest.CoreMode.Gen.CarryNzList'
    t = [header(mod, 'The nonzero facts\' carried parameters, callee words and own values (`Res.carryNzG`).')]
    t.append('namespace LeanVM.Guest.Res\n\n@[expose] public section\n\n')
    t.append('/-- **The parameters carried nonzero in `K`**: callee, parameter position. -/\n'
             'def carriedNz : List (String × Nat) := [\n%s]\n\n' % ',\n'.join(
                 '  ("%s", %d)' % (f, p) for f in sorted(carried) for p in sorted(carried[f])))
    t.append('/-- **The callee words nonzero in `K`**: callee, position among its parameters then its returns. -/\n'
             'def nzUp : List (String × Nat) := [\n%s]\n\n' % ',\n'.join('  ("%s", %d)' % c for c in up))
    t.append('/-- **The own values pinned nonzero in `K`** by their function\'s body (`Res.ownChk`): function, value number. -/\n'
             'def ownNz : List (String × Nat) := [\n%s]\n\nend\n\nend LeanVM.Guest.Res\n' % ',\n'.join(
                 '  ("%s", %d)' % c for c in own))
    files[mod] = ''.join(t)
    n = resgen.coreCount()
    ranges = [(a, (n - a) if m is None else m) for a, m in RANGES]
    assert sum(m for _, m in ranges) == n and all(m > 0 for _, m in ranges), ranges
    mods = []
    for k, (a, m) in enumerate(ranges):
        mod = 'LeanVM.Guest.CoreMode.Gen.CarryCallers%d' % k
        t = [header(mod, 'The carried and nonzero facts\' checks, functions %d to %d.' % (a, a + m - 1))]
        t.append('public import LeanVM.Guest.CoreMode.Fam.CarryDefs\n\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n'
                 'public section\n\ntheorem carry_%d : RangeOk (fun _ fn => carryG fn) %d %d := by\n'
                 '  unfold RangeOk; decide +kernel\n\n'
                 'theorem carryNz_%d : RangeOk (fun _ fn => carryNzG fn) %d %d := by\n'
                 '  unfold RangeOk; decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n' % (a, a, m, a, a, m))
        files[mod] = ''.join(t); mods.append(mod)
    mod = 'LeanVM.Guest.CoreMode.Gen.CarryOk'
    t = [header(mod, 'The carried and nonzero facts\' checks, every function.')]
    t.append(''.join('public import %s\n' % m for m in mods))
    t.append('public import LeanVM.Guest.CoreMode.Fam.LinkDefs\n')
    t.append('\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest LeanVM.Guest.Memory\n\npublic section\n\n')
    for name, chk, what in (('carry', 'carryG', 'carried'), ('carryNz', 'carryNzG', 'nonzero')):
        app = '%s_0' % name
        for a, m in ranges[1:]: app = '(%s.append %s_%d)' % (app, name, a)
        t.append('/-- **The %s facts\' check, every function.** -/\n'
                 'theorem %s_all : ∀ fn ∈ coreProgram, %s fn = true := by\n'
                 '  have h := %s\n'
                 '  have h\' : RangeOk (fun _ fn => %s fn) 0 coreProgram.length := by\n'
                 '    rw [coreProgram_length]; exact h\n  exact rangeOk_all h\'\n\n' % (what, name, chk, app, chk))
    t.append('end\n\nend LeanVM.Guest.Res\n')
    files[mod] = ''.join(t)
    return {os.path.join(OUT, m.split('.')[-1] + '.lean'): v for m, v in files.items()}


def main(argv):
    files = render()
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'CarryCallers*.lean')), '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('Carry: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
