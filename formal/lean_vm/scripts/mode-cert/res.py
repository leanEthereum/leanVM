"""Writes `Guest/Mode/ResData.lean`: the mode walk's residuals by family (`Guest/Mode/ResFam.lean`),
read off the walk's checks `gen.py` wrote (`Pack/*/Mode{k}.lean`, `ModeD{k}.lean`), each family's
functions with the kernel's check that their residuals have its shape. Run after `gen.py`.
`--check` writes nothing and fails when the file differs; `--list` prints each function's residuals.
Usage: python3 -I scripts/mode-cert/res.py [--check] [--list]"""
import sys, os, re, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import data

PACKS = os.path.join(data.ROOT, 'Pack')
OUT = os.path.join(data.ROOT, 'Mode', 'ResData.lean')

TOK = re.compile(r'\s*(⟨|⟩|\(|\)|\[|\]|,|"[^"]*"|[^\s⟨⟩()\[\],]+)')


def toks(s):
    out = []; i = 0
    while i < len(s):
        m = TOK.match(s, i)
        if not m or m.end() == i: break
        if m.group(1): out.append(m.group(1))
        i = m.end()
    return out


def parse(ts, i=0):
    """A literal as nested lists: `(f a b)` and `⟨a, b⟩` and `[a, b]` as ('app'|'tup'|'list', items)."""
    t = ts[i]
    if t in '(⟨[':
        close = {'(': ')', '⟨': '⟩', '[': ']'}[t]; items = []; i += 1
        while ts[i] != close:
            if ts[i] == ',': i += 1; continue
            x, i = parse(ts, i); items.append(x)
        kind = {'(': 'app', '⟨': 'tup', '[': 'list'}[t]
        return (kind, items), i + 1
    return t, i + 1


def app(x):
    """`(f a b)` and bare `f` as (f, [a, b])."""
    if isinstance(x, tuple) and x[0] == 'app': return x[1][0], x[1][1:]
    return x, []


def flat(x, defs):
    """A literal list, `List.flatten` nests included."""
    if isinstance(x, str) and x in defs: return flat(defs[x], defs)
    if x[0] == 'list': return x[1]
    f, a = app(x)
    assert f == 'List.flatten', x
    return [y for l in flat(a[0], defs) for y in flat(l, defs)]


def trie(x, defs):
    """A literal `Exec.Trie` as {key: value}."""
    out = {}
    def go(x, k, step):
        if isinstance(x, str) and x in defs: return go(defs[x], k, step)
        f, a = app(x)
        if f == '.nil': return
        assert f == '.node', f
        here, l, r = a
        hf, ha = app(here)
        if hf == 'some': out[k] = ha[0]
        go(l, k + step, 2 * step); go(r, k + 2 * step, 2 * step)
    go(x, 0, 1)
    return out


def num(x): return int(x)


def base(x):
    f, a = app(x)
    return ('fr', num(a[0])) if f == '.fr' else ('hp', num(a[0]), num(a[1]))


def idx(x):
    f, a = app(x)
    return ('num', num(a[0])) if f == '.num' else ('ex', base(a[0]), num(a[1]))


def res(x, defs):
    f, a = app(x)
    if f == '.nz': return ('nz', num(a[0]))
    if f == '.lt': return ('lt', idx(a[0]), idx(a[1]))
    if f == '.sub': return ('sub', a[0], flat(a[1], defs))
    return (f[1:],) + tuple(a)


def defsOf(blk):
    """Each `noncomputable def NAME : T :=` literal of a namespace block."""
    out = {}
    for m in re.finditer(r'noncomputable def (\w+) : [^\n]*:=\n', blk):
        start = m.end(); end = blk.find('\n\n', start)
        out[m.group(1)] = parse(toks(blk[start:end]))[0]
    return out


def load():
    """Each checked function's residuals {offset: [res]} and the module defining its `modeFun`."""
    fns = {}
    for path in sorted(glob.glob(os.path.join(PACKS, '*', 'Mode*.lean'))):
        b = os.path.basename(path)[:-5]
        if not re.fullmatch(r'Mode\d+|ModeD\d+', b): continue
        p = path.split(os.sep)[-2]
        t = open(path).read()
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.«')[1:]:
            n = blk.split('»', 1)[0]
            if 'def modeFun' not in blk: continue
            defs = defsOf(blk)
            fun = defs['modeFun'][1]
            rs = {i: [res(r, defs) for r in flat(l, defs)] for i, l in trie(fun[4], defs).items()}
            fns[n] = dict(mod='LeanVM.Guest.Pack.«%s».%s' % (p, b), res=rs)
    return fns


def mono(x):
    fp, k, bs = x[1]
    return (num(fp), num(k), tuple((base(app(b)[0]), num(app(b)[1][0])) for b in bs[1]))


def rng(x):
    q, lo, hi, S, d = x[1]
    return (mono(q), idx(lo), idx(hi), num(S), num(d))


def subBound(a, bs):
    return len(bs) == 1 and bs[0][0] == a[0] and bs[0][3] == a[3] and bs[0][4] == a[4]


def subTab(a, bs):
    if not bs: return False
    b = bs[0]
    return (a[1] == ('num', 0) and a[2] == ('num', b[3]) and a[3] == 1 and a[4] == 0
            and all(c[:4] == b[:4] for c in bs) and [c[4] for c in bs] == list(range(b[3])))


def oblFam(r):
    if r[0] == 'nz': return True
    if r[0] == 'lt': return r[1][0] == 'ex' and r[1][2] == 0 and r[2][0] == 'num'
    if r[0] == 'sub':
        a = rng(r[1]); bs = [rng(b) for b in r[2]]
        return subBound(a, bs) or subTab(a, bs)
    return False


def nzAt(code, i, r):
    return r[0] != 'nz' or (code[i][0] == 'mul' and int(code[i][1][1]) == r[1])


def winAt(q, n, N, r):
    if r[0] != 'lt': return True
    a, b = r[1], r[2]
    return a[0] == 'ex' and a[1][0] == 'hp' and a[1][1] == q and a[1][2] < n and a[2] == 0 and b == ('num', N)


def frs(f):
    """The frame cell bounds `(o, N)` of a function's order residuals."""
    return {(r[1][1][1], r[2][1]) for rs in f['res'].values() for r in rs
            if r[0] == 'lt' and r[1][0] == 'ex' and r[1][1][0] == 'fr' and r[1][2] == 0 and r[2][0] == 'num'}


def lts(f): return [r for rs in f['res'].values() for r in rs if r[0] == 'lt']


def fnq(n): return 'Fn.«%s»' % n


def entry(n, *extra):
    return '(%s)' % ', '.join(['%s.modeFun' % fnq(n), '%s.code.chunks.flatten' % fnq(n)] + [str(e) for e in extra])


def listDef(name, typ, doc, rows):
    return '/-- %s -/\nnoncomputable def %s : List (%s) := [\n  %s]\n\n' % (doc, name, typ, ',\n  '.join(rows))


def thm(name, doc, lst, prop):
    return ('/-- %s -/\ntheorem %s : ∀ p ∈ %s, %s := by\n  simp only [%s, List.forall_mem_cons, List.not_mem_nil, '
            'false_imp_iff, implies_true, and_true]\n  decide +kernel\n\n') % (doc, name, lst, prop, lst)


def render(F, D):
    code = {f['ns']: f['code'] for f in D['fns'].values()}
    withRes = sorted(n for n, f in F.items() if any(f['res'].values()))
    nz = [n for n in withRes if any(r[0] == 'nz' for rs in F[n]['res'].values() for r in rs)]
    for n in nz:
        assert all(nzAt(code[n], i, r) for i, rs in F[n]['res'].items() for r in rs), n
    wp = []
    for n in withRes:
        m = re.fullmatch(r'walk_path__L(\d+)_L(\d+)', n)
        if m and lts(F[n]):
            k = (int(m.group(1)) + 5) // 6
            assert all(winAt(4, k, 64, r) for rs in F[n]['res'].values() for r in rs), n
            wp.append((n, k))
    fr = [(n, *next(iter(frs(F[n])))) for n in withRes if lts(F[n]) and len(frs(F[n])) == 1 and len(frs(F[n])) and
          all(r[1][0] == 'ex' and r[1][1][0] == 'fr' for r in lts(F[n]))]
    fam = [n for n in withRes if all(oblFam(r) for rs in F[n]['res'].values() for r in rs)]
    rest = [n for n in withRes if n not in fam]
    mods = sorted({F[n]['mod'] for n in withRes})
    out = ['/-\n  LeanVM.Guest.Mode.ResData\n\n  Generated by `scripts/mode-cert/res.py`; do not edit.\n'
           "  The mode walk's residuals by family, checked on the guest's data.\n-/\n\nmodule\n\n"]
    out.append('public import LeanVM.Guest.Mode.ResFam\n')
    out.append(''.join('public import %s\n' % m for m in mods))
    out.append('\n/-!\n# The residuals\' families, checked on the guest\'s data\n\n')
    out.append('`nzMul_guest`: each nonzero residual of a kernel-checked function sits at a `MUL` as its divisor '
               '(`nz_mul`, `resRef_obl`: its product cell nonzero on the reference). `ltWin_guest`: each order residual '
               'of a `walk_path` specialization `walk_path__L{p}_L{c}` bounds a window of its `wins` argument (frame '
               'cell `4`): the exponent of the word `k < (p + 5) / 6` cells past it below `64` (`obl_win`, '
               '`rwins_of_winsAt`). `ltFr_guest`: each order residual of the listed functions bounds a frame cell\'s '
               'exponent. `famOk_guest`: every residual of the listed functions has an obligation of its own (`Obl`, '
               '`oblFam`).')
    out.append(' The functions with a residual outside the families: %s.\n-/\n\n' % (
        ', '.join('`%s`' % n for n in rest) if rest else 'none'))
    out.append('namespace LeanVM.Guest.Mode\n\nopen LeanVM.Guest\n\n@[expose] public section\n\n')
    out.append(listDef('nzFns', 'Fun × List OffsetInstruction',
                       'The kernel-checked functions with nonzero residuals: their walks\' data and code.',
                       [entry(n) for n in nz]))
    out.append(thm('nzMul_guest', '**Every nonzero residual of the guest\'s checked functions is a `MUL`\'s divisor.**',
                   'nzFns', 'nzMul p.1 p.2 = true'))
    out.append(listDef('wpFns', 'Fun × List OffsetInstruction × ℕ',
                       '`walk_path`\'s specializations: their walks\' data and code, and their positions\' window count.',
                       [entry(n, k) for n, k in wp]))
    out.append(thm('ltWin_guest', '**Every order residual of `walk_path` bounds a window.**', 'wpFns',
                   'ltWin p.1 p.2.1.length 4 p.2.2 64 = true'))
    out.append(listDef('frFns', 'Fun × List OffsetInstruction × ℕ × ℕ',
                       'The functions whose order residuals bound one frame cell\'s exponent: their walks\' data and '
                       'code, the cell and the bound.', [entry(n, o, N) for n, o, N in fr]))
    out.append(thm('ltFr_guest', '**Every order residual of the listed functions bounds its frame cell.**', 'frFns',
                   'ltFr p.1 p.2.1.length p.2.2.1 p.2.2.2 = true'))
    out.append(listDef('famFns', 'Fun × List OffsetInstruction',
                       'The kernel-checked functions with residuals all in the families.', [entry(n) for n in fam]))
    out.append(thm('famOk_guest', '**Every residual of the listed functions has an obligation of its own.**', 'famFns',
                   'famOk p.1 p.2.length = true'))
    out.append('end\n\nend LeanVM.Guest.Mode\n')
    return ''.join(out)


def main(argv):
    F = load()
    if '--list' in argv:
        import collections
        for n, f in sorted(F.items()):
            c = collections.Counter(r[0] for rs in f['res'].values() for r in rs)
            if c: print(n, f['mod'], dict(c))
        return
    text = render(F, data.load())
    old = open(OUT).read() if os.path.exists(OUT) else None
    if old == text: print('ResData: unchanged'); return
    if '--check' in argv: print('stale:', OUT); sys.exit(1)
    open(OUT, 'w').write(text); print('ResData: written')


if __name__ == '__main__':
    main(sys.argv[1:])
