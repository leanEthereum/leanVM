"""The core route of milestone 1 (`formal/notes/core-mode.md`, `Guest/CoreMode/Core.lean`): the functions
passing `heapOk` and the pairing whose body is straight-line, whose only `JUMP` is its last
instruction, a return the pairing takes by its head statement, and whose signature its callers know
(`Mode.Sig`, `Pack/*/ModeSig.lean`) promises only frame cells, heap cells and runs of constant bounds over
its parameters (and returned products `retV`, each a returned value's monomial); each with the heap cells it promises (`CFun.post`) and their witnesses, the preconditions
the heap check then names (`HCert.sig.pre`), its pairing's oracle and stores. Which functions take the
route; the kernel's checks (`CoreMode.CoreOk`) confirm it.

`route()` returns `{name: dict(post=[(cell, wit)], pre=[cell], O=[..], S=[..], pack, bpack, j)}`, cells as
`(bases, off)`, bases `((value number, exponent), ...)`, witnesses `('ev', n)` or `('pre', k)`.
Usage (a census): python3 -I scripts/core-mode/route.py"""
import os, re, sys, glob, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import heap  # noqa: E402

GUEST = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
FIELDS = 'pc entry self pre preR term ret post postR postL preP postP postLP retV postT postC'.split()


def tokens(s):
    return re.findall(r'⟨|⟩|\[|\]|\(|\)|,|[A-Za-z_.][A-Za-z_.0-9]*|\d+', s)


def parse(s):
    """A printed Lean term of `Mode.Sig`'s parts as Python: anonymous constructors as tuples, lists as
    lists, `.c a b` as `('c', a, b)`, `List.flatten l` flattened."""
    ts = tokens(s); pos = [0]

    def term():
        t = ts[pos[0]]
        if t == '⟨':
            pos[0] += 1; out = []
            while ts[pos[0]] != '⟩':
                out.append(app())
                if ts[pos[0]] == ',': pos[0] += 1
            pos[0] += 1
            return tuple(out)
        if t == '[':
            pos[0] += 1; out = []
            while ts[pos[0]] != ']':
                out.append(app())
                if ts[pos[0]] == ',': pos[0] += 1
            pos[0] += 1
            return out
        if t == '(':
            pos[0] += 1; vs = [app()]
            while ts[pos[0]] == ',':
                pos[0] += 1; vs.append(app())
            assert ts[pos[0]] == ')', (s, pos[0]); pos[0] += 1
            return vs[0] if len(vs) == 1 else tuple(vs)
        pos[0] += 1
        if t.isdigit(): return int(t)
        return ('id', t)

    def app():
        head = term()
        args = []
        while pos[0] < len(ts) and ts[pos[0]] not in (',', ')', ']', '⟩'):
            args.append(term())
        if not args: return head
        h = head[1]
        if h == 'List.flatten': return [x for l in args[0] for x in l]
        return (h.lstrip('.'),) + tuple(args)

    return app()


def split_top(s):
    out = []; depth = 0; cur = ''
    for ch in s:
        if ch in '⟨([{': depth += 1
        if ch in '⟩)]}': depth -= 1
        if ch == ',' and depth == 0: out.append(cur.strip()); cur = ''
        else: cur += ch
    out.append(cur.strip())
    return out


def sigs():
    """Each function's `Mode.Sig`, by namespace name, fields parsed."""
    out = {}
    for f in glob.glob(os.path.join(GUEST, 'Pack', '*', 'ModeSig.lean')):
        t = open(f).read()
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.')[1:]:
            nm = blk.split('\n', 1)[0].strip().strip('«»')
            m = re.search(r'def modeSig : Mode.Sig :=\s*⟨(.*?)⟩\n\ntheorem', blk, re.S)
            parts = split_top(m.group(1))
            assert len(parts) == 16, nm
            out[nm] = {k: parse(v) for k, v in zip(FIELDS, parts)}
    return out


def mono_cell(G, np, m):
    """`monoC` with `monoOk`: the cell `(bases, off)` over parameter numbers, or None."""
    fp, k, bs = m
    if fp != 0: return None
    out = []
    for b, e in bs:
        if b[0] != 'fr': return None
        o = b[1]
        if not (o in G['entry'] and 2 <= o and o - 2 < np and o < 2 ** 28): return None
        out.append((o - 2, e))
    return (tuple(out), k)


def hp_val(body, k, d):
    """The value a top-level `load` reads at parameter `k`'s word past `d`, before any `ret` (`CoreMode.hpVal`)."""
    for s in body:
        if s[0] == 'ret': return None
        if s[0] == 'a' and s[1][0] == 'load' and s[1][2] == k and s[1][3] == d: return s[1][1]
    return None


def mono_post(G, np, m, body, loc):
    """`monoF (baseOfP ..)` with `monoOkP`: a promised product's cell, its bases parameters' frame cells, return
    cells' returned values, words past parameters' a top-level `load` reads; or None."""
    fp, k, bs = m
    if fp != 0: return None
    out = []
    for b, e in bs:
        if b[0] == 'fr':
            o = b[1]
            if not (o < 2 ** 28 and ((o in G['entry'] and 2 <= o and o - 2 < np) or o in G['ret'])): return None
            if 2 <= o and o - 2 < np:
                out.append((o - 2, e)); continue
            vs = next((s[1] for s in body if s[0] == 'ret'), None)
            v = next((v for v in vs if loc(v) == o), None) if vs is not None else None
            if v is None: return None
            out.append((v, e))
        elif b[0] == 'hp':
            q, d = b[1], b[2]
            if not (q in G['entry'] and 2 <= q and q - 2 < np and q < 2 ** 28): return None
            v = hp_val(body, q - 2, d)
            if v is None: return None
            out.append((v, e))
        else:
            return None
    return (tuple(out), k)


def promised(G, np, body=(), loc=lambda v: None):
    """The heap cells the signature promises (`post`, `postR`'s points), or None if it promises more."""
    if G['self'] != ('id', 'none'): return None
    for k in ('term', 'postL', 'postP', 'postLP', 'postT', 'postC'):
        if G[k] != []: return None
    cells = []
    for m in G['post']:
        c = mono_post(G, np, m, body, loc)  # `CoreMode.sigOk`'s `postIn`
        if c is None: return None
        cells.append(c)
    for q, lo, hi, S, d in G['postR']:
        c = mono_post(G, np, q, body, loc)
        if c is None or lo[0] != 'num' or hi[0] != 'num': return None
        a, b = lo[1], hi[1]
        cells += [(c[0], c[1] + S * (a + j) + d) for j in range(b - a)]
    return cells


def run_points(G, np):
    """The points of the signature's preconditions' runs of constant bounds (`CoreMode.preIn`)."""
    out = []
    for q, lo, hi, S, d in G['preR']:
        c = mono_cell(G, np, q)
        if c is None or lo[0] != 'num' or hi[0] != 'num': continue
        out += [(c[0], c[1] + S * (lo[1] + j) + d) for j in range(hi[1] - lo[1])]
    return out


def straight(body):
    return all(s[0] in ('ret', 'a') for s in body)


def no_ret(ss):
    """A block with no `ret` and no call: atoms, branches and `match`es (`CoreMode.blockB`)."""
    for s in ss:
        if s[0] == 'a': continue
        if s[0] == 'ite':
            if not (no_ret(s[2]) and no_ret(s[3])): return False
        elif s[0] == 'match':
            if not all(no_ret(a) for a in s[2]): return False
        else: return False
    return True


def ints(x):
    """The numbers in a term: an atom's values, over-approximated (offsets, constants)."""
    if isinstance(x, int): return [x]
    if isinstance(x, (list, tuple)): return [n for y in x for n in ints(y)]
    return []


def sel_ok(body, params=()):
    """Each `match` and `dispatch` at the top level, its selector used by a top-level atom before it (a dispatch's, or a
    parameter), no `match` nested, none past a `ret` (`CoreMode.selGo`)."""
    def has_match(ss):
        for s in ss:
            if s[0] == 'match': return True
            if s[0] == 'ite' and (has_match(s[2]) or has_match(s[3])): return True
        return False
    seen = set()
    for n, s in enumerate(body):
        if s[0] == 'a':
            seen.update(ints(s[1][1:]))
        elif s[0] == 'match':
            if s[1] not in seen or any(has_match(a) for a in s[2]): return False
        elif s[0] == 'dispatch':
            if s[1] not in seen and s[1] not in params: return False
        elif s[0] == 'ite':
            if has_match(s[2]) or has_match(s[3]): return False
        elif s[0] == 'ret':
            return not has_match(body[n + 1:]) and not any(x[0] == 'dispatch' for x in body[n + 1:])
    return True


def branchy(body):
    """A body of atoms, branches and `match`es with no `ret` or call in them, and `ret`s (`CoreMode.bodyB`)."""
    return all(s[0] in ('ret', 'a') or (s[0] in ('ite', 'match') and no_ret([s])) for s in body)


def frame_nzr():
    """The functions whose frame walk (`CoreMode/Pack/*/Frame*.lean`) relies on residual divisors (`FFun.nzr`),
    and those whose walk is told callees' signatures (`FFun.sigs`)."""
    out = set(); calls = set()
    for f in glob.glob(os.path.join(GUEST, 'CoreMode', 'Pack', '*', 'Frame*.lean')):
        t = open(f, encoding='utf-8').read()
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.«')[1:]:
            n = blk.split('»', 1)[0]
            m = re.search(r'def frameFun : CoreMode.FFun :=\s*⟨(.*?)⟩\n\n', blk, re.S)
            if m and split_top(m.group(1))[7] != '.nil': out.add(n)
            if m and split_top(m.group(1))[4] != '.nil': calls.add(n)
    return out, calls


def route(verbose=False):
    import pair
    S = sigs()
    global NZR
    NZR, CALLS = frame_nzr()
    P, _ = pair.collect()
    AL = pair.AL
    fns = AL.functions()
    pows = AL.pow_table()
    out = {}; why = collections.Counter()
    for k, pf in sorted(P.items()):
        params, body = heap.CORE[k]
        if pf.get('kind') in ('c', 'l', 'lc'):
            # a body with calls (`callc.py`), a leaf loop helper (`loopc.py`) or one with calls (`loopcc.py`), its
            # certificate by the check with calls
            out[k] = dict(post=[], pre=[], O=pf['O'], S=pf['S'], j=pf['j'], bpack=pf['bpack'], kind=pf['kind'])
            continue
        F = fns[k]
        ns = F.get('ns', k)
        G = S.get(ns) or S.get(k)
        if not branchy(body): why['not straight'] += 1; continue
        if not sel_ok(body, params): why['selector'] += 1; continue
        if k in CALLS: why['callees'] += 1; continue
        if F['name'] == 'main' or F['stat'].get(1) == ('fpg', 0, 0): why['main'] += 1; continue
        ex, locs = pf['extra'], pf['locs']
        loc = lambda v: ex[v] if v in ex else (locs[v] if v < len(locs) else 0)
        cells = promised(G, len(params), body, loc)
        if cells is None: why['signature'] += 1; continue
        f = heap.Fn(k)
        stf = f.block([{}, {}, 0], f.body)
        rets = [s[1] for s in body if s[0] == 'ret'][0]
        if not all(o < 2 ** 28 and o in G['ret'] and mono_cell(G, len(params), m) is not None and
                   any(f.mono(stf[0], v) == mono_cell(G, len(params), m) for v in rets) for o, m in G['retV']):
            why['returned product'] += 1; continue
        post = []
        for c in cells:
            w = f.witness(stf[1], subst(f, stf[0], c))
            if w is None: break
            post.append((c, w))
        else:
            pre_ok = all(any(mono_cell(G, len(params), m) == c for m in G['pre']) or c in run_points(G, len(params))
                         for c in f.pre)
            if not pre_ok: why['precondition'] += 1; continue
            out[k] = dict(post=post, pre=list(f.pre), O=pf['O'], S=pf['S'], j=pf['j'], bpack=pf['bpack'], kind='m1')
            continue
        why['unwritten promise'] += 1
    if verbose:
        print('route', len(out), 'of', len(P), dict(why))
    return out


def subst(f, env, c):
    """A cell's monomial in the heap pass's environment (`CoreMode.substC`)."""
    bs, off = c
    acc = ((), off)
    for k, e in reversed(bs):
        m = f.mono(env, k)
        p = ((), 0)
        for _ in range(e):
            p = (heap.merge(p[0], m[0]), p[1] + m[1])
        acc = (heap.merge(p[0], acc[0]), p[1] + acc[1])
    return acc


def _cell(c):
    return (tuple(tuple(b) for b in c[0]), c[1])


def route_sub():
    """`route()` in a fresh interpreter (the generators' own `data` modules clash with the pairing's)."""
    import subprocess, tempfile, json
    with tempfile.NamedTemporaryFile(suffix='.json') as fh:
        subprocess.run([sys.executable, '-I', os.path.abspath(__file__), '--dump', fh.name], check=True,
                       stdout=subprocess.DEVNULL)
        R = json.load(open(fh.name))
    for r in R.values():
        r['post'] = [(_cell(c), tuple(w)) for c, w in r['post']]
        r['pre'] = [_cell(c) for c in r['pre']]
    return R


if __name__ == '__main__':
    R = route(verbose=True)
    if '--dump' in sys.argv:
        import json
        json.dump(R, open(sys.argv[sys.argv.index('--dump') + 1], 'w'))
