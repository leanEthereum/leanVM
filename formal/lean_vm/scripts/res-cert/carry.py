"""Writes `Guest/Res/CarryNzList.lean`, `CarryCallers{k}.lean` and `CarryOk.lean`: the carried facts' check
(`Res.carryG`: every call site passes the listed callees' carried facts, every heap witness pointer its spine does not
pin is in `K` by the carried values) and the nonzero facts' check (`Res.carryNzG`: every call site passes its callees'
nonzero parameters, every dynamic allocation's size is nonzero in `K`, every listed callee word is) over the whole
program by ranges, and their conjunctions. The carried parameters of `carryG` are `Res.carried` (`Res/CarryDefs.lean`);
those of `carryNzG` (`Res.carriedNz`) and its callee words (`Res.nzUp`) are derived here, by mirroring the check over
the core IR (`Pack/*/Core*.lean`) to a fixed point, and written to `CarryNzList.lean`. `--check` writes nothing and
fails when a file differs.
Usage: python3 -I scripts/res-cert/carry.py [--check]"""
import sys, os, glob, re, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import term
import link

_spec = importlib.util.spec_from_file_location('bcdata', os.path.join(HERE, '..', 'bridge-cert', 'data.py'))
bc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(bc)

OUT = term.OUT
# by ranges of functions, each a kernel check; `main` (function 0) alone
RANGES = [(0, 1), (1, 10), (11, 1), (12, 1), (13, 7), (20, 10), (30, 10), (40, 60), (100, 300), (400, 400), (800, 400), (1200, 200), (1400, None)]
# `Res.nzDepth`, `Res.kDepth`
NZ_DEPTH, K_DEPTH = 12, 8


# ---- the core IR, as `Res.carryNzG` reads it -------------------------------------------------------------------------

def atom(e, env):
    h, a = bc.head(e)
    v = bc.val
    if h == '.const':
        w = a[1]
        return ('const', v(a[0]), (w[2][0], w[2][1]) if isinstance(w, tuple) and w[0] == 'app' and w[1] == ('id', 'word')
                else None)
    if h in ('.mul', '.add'):
        return (h[1:], v(a[0]), v(a[1]), v(a[2]))
    if h == '.copy':
        return ('copy', v(a[0]), v(a[1]))
    if h in ('.load', '.touch'):
        return (h[1:], v(a[0]), v(a[1]))
    if h == '.rangeCheck':
        return ('rangeCheck', v(a[0]), v(a[1]))
    if h == '.frameAddr':
        return ('frameAddr', v(a[0]))
    if h == '.assertInK':
        return ('assertInK', v(a[0]), v(a[1]))
    if h == '.hint':
        hh, ha = bc.head(a[0])
        if hh == '.allocDyn':
            return ('allocDyn', v(ha[0]), v(ha[1]))
    return ('other',)


def stmt(e, env):
    h, a = bc.head(e)
    if h == '.atom':
        return ('atom', atom(a[0], env))
    if h == '.ite':
        return ('ite', bc.val(a[0]), block(a[1], env), block(a[2], env))
    if h == '.match_':
        return ('match', bc.val(a[0]), [block(x, env) for x in bc.as_list(a[1], env)])
    if h == '.call':
        return ('call', a[0][1], bc.vals(a[1], env), bc.vals(a[2], env))
    if h == '.callIf':
        return ('callIf', bc.val(a[0]), a[1][1], bc.vals(a[2], env))
    if h == '.dispatch':
        return ('dispatch', bc.val(a[0]), [x[1] for x in bc.as_list(a[1], env)], bc.vals(a[2], env),
                bc.vals(a[3], env))
    if h == '.ret':
        return ('ret', bc.vals(a[0], env))
    raise ValueError(h)


def block(e, env):
    return [stmt(x, env) for x in bc.as_list(e, env)]


def functions():
    """Each core function by name: its parameter count, loop flag (`Fn.loop`) and body."""
    F = {}
    for text in bc.core_texts().values():
        name = re.search(r'name := "([^"]*)"', text).group(1)
        ds = bc.defs(text[text.index('namespace core'):])
        cache = {}

        def env(n):
            if n not in cache:
                cache[n] = bc.parse(ds[n])
            return cache[n]
        body = block(env('body'), env)
        params = [int(x) for x in re.findall(r'\.n (\d+)', re.search(r'params := ([^\n]*)', text).group(1))]
        assert params == list(range(len(params))), name
        loop = len(body) >= 2 and body[-1] == ('ret', []) and body[-2][0] == 'callIf' and body[-2][2] == name
        F[name] = dict(np=len(params), loop=loop, body=body)
    return F


# ---- the check, mirrored -------------------------------------------------------------------------------------------

def no_ret(ss):
    for s in ss:
        if s[0] == 'ret' or (s[0] == 'ite' and not (no_ret(s[2]) and no_ret(s[3]))) or \
                (s[0] == 'match' and not all(no_ret(x) for x in s[2])):
            return False
    return True


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

    def pin_in(self, e, v):
        if e[0] != 'a':
            return False
        a = e[1]
        return (a[0] in ('load', 'touch') and a[2] == v) or (a[0] in ('rangeCheck', 'assertInK') and v in a[1:3]) or \
            (a[0] == 'frameAddr' and a[1] == v) or (a[0] == 'const' and a[1] == v and a[2] is not None and a[2][1] == 0)

    def k_in(self, kv, sp, n, v):
        if v in kv or any(self.pin_in(e, v) for e in sp):
            return True
        return n > 0 and any(e[0] == 'a' and e[1][0] == 'mul' and e[1][1] == v and self.k_in(kv, sp, n - 1, e[1][2]) and
                             self.k_in(kv, sp, n - 1, e[1][3]) for e in sp)

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
            elif a[0] == 'copy':
                d, s = a[1:]
                if (d == v and self.nz(kv, sp, n - 1, s)) or (s == v and self.nz(kv, sp, n - 1, d)):
                    return True
        return False

    def kv(self, f):
        """`Res.kvNz`."""
        return sorted(self.carried.get(f, ())) + ([0] if self.F[f]['loop'] else [])

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
    return carried, up, bad


# ---- the modules ---------------------------------------------------------------------------------------------------

def header(mod, what):
    return '/-\n  %s\n\n  Generated by `scripts/res-cert/carry.py`; do not edit.\n  %s\n-/\n\nmodule\n\n' % (mod, what)


def render():
    files = {}
    F = functions()
    carried, up, bad = nz_lists(F)
    if bad:
        sys.exit('carry: the nonzero facts\' check fails:\n  ' + '\n  '.join(map(str, bad)))
    assert 'main' not in carried
    mod = 'LeanVM.Guest.Res.CarryNzList'
    t = [header(mod, 'The nonzero facts\' carried parameters and callee words (`Res.carryNzG`).')]
    t.append('namespace LeanVM.Guest.Res\n\n@[expose] public section\n\n')
    t.append('/-- **The parameters carried nonzero in `K`**: callee, parameter position. -/\n'
             'def carriedNz : List (String × Nat) := [\n%s]\n\n' % ',\n'.join(
                 '  ("%s", %d)' % (f, p) for f in sorted(carried) for p in sorted(carried[f])))
    t.append('/-- **The callee words nonzero in `K`**: callee, position among its parameters then its returns. -/\n'
             'def nzUp : List (String × Nat) := [\n%s]\n\nend\n\nend LeanVM.Guest.Res\n' % ',\n'.join(
                 '  ("%s", %d)' % c for c in up))
    files[mod] = ''.join(t)
    n = link.coreCount()
    ranges = [(a, (n - a) if m is None else m) for a, m in RANGES]
    assert sum(m for _, m in ranges) == n
    mods = []
    for k, (a, m) in enumerate(ranges):
        mod = 'LeanVM.Guest.Res.CarryCallers%d' % k
        t = [header(mod, 'The carried and nonzero facts\' checks, functions %d to %d.' % (a, a + m - 1))]
        t.append('public import LeanVM.Guest.Res.CarryDefs\n\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n'
                 'public section\n\ntheorem carry_%d : RangeOk (fun _ fn => carryG fn) %d %d := by\n'
                 '  unfold RangeOk; decide +kernel\n\n'
                 'theorem carryNz_%d : RangeOk (fun _ fn => carryNzG fn) %d %d := by\n'
                 '  unfold RangeOk; decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n' % (a, a, m, a, a, m))
        files[mod] = ''.join(t); mods.append(mod)
    mod = 'LeanVM.Guest.Res.CarryOk'
    t = [header(mod, 'The carried and nonzero facts\' checks, every function.')]
    t.append(''.join('public import %s\n' % m for m in mods))
    t.append('public import LeanVM.Guest.Res.LinkDefs\n')
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
    files = render(); bad = []
    for p in glob.glob(os.path.join(OUT, 'CarryCallers*.lean')):
        if p not in files:
            bad.append(p)
            if '--check' not in argv: os.remove(p)
    for p, text in sorted(files.items()):
        old = open(p).read() if os.path.exists(p) else None
        if old == text: continue
        bad.append(p)
        if '--check' not in argv: open(p, 'w').write(text)
    if '--check' in argv and bad: print('stale:', *bad, sep='\n  '); sys.exit(1)
    print('Carry: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
