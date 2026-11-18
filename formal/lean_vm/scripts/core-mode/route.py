"""The core route of milestone 1 (`formal/notes/core-mode.md`, `Guest/CoreMode/Core.lean`): the functions
passing `heapOk` and the pairing whose body is straight-line, whose only `JUMP` is its last
instruction, a return the pairing takes by its head statement, and whose signature its callers know
(`Mode.Sig`, `Pack/*/ModeSig.lean`) promises only frame cells, heap cells and runs of constant bounds over
its parameters; each with the heap cells it promises (`CFun.post`) and their witnesses, the preconditions
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


def promised(G, np):
    """The heap cells the signature promises (`post`, `postR`'s points), or None if it promises more."""
    if G['self'] != ('id', 'none'): return None
    for k in ('term', 'postL', 'postP', 'postLP', 'retV', 'postT', 'postC'):
        if G[k] != []: return None
    cells = []
    for m in G['post']:
        c = mono_cell(G, np, m)
        if c is None: return None
        cells.append(c)
    for q, lo, hi, S, d in G['postR']:
        c = mono_cell(G, np, q)
        if c is None or lo[0] != 'num' or hi[0] != 'num': return None
        a, b = lo[1], hi[1]
        cells += [(c[0], c[1] + S * (a + j) + d) for j in range(b - a)]
    return cells


def straight(body):
    return all(s[0] in ('ret', 'a') for s in body)


def frame_nzr():
    """The functions whose frame walk (`CoreMode/Pack/*/Frame*.lean`, `FFun.nzr`) relies on residual divisors."""
    out = set()
    for f in glob.glob(os.path.join(GUEST, 'CoreMode', 'Pack', '*', 'Frame*.lean')):
        t = open(f, encoding='utf-8').read()
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.«')[1:]:
            n = blk.split('»', 1)[0]
            m = re.search(r'def frameFun : CoreMode.FFun :=\s*⟨(.*?)⟩\n\n', blk, re.S)
            if m and split_top(m.group(1))[7] != '.nil': out.add(n)
    return out


def route(verbose=False):
    import pair
    S = sigs()
    global NZR
    NZR = frame_nzr()
    P, _ = pair.collect()
    AL = pair.AL
    fns = AL.functions()
    pows = AL.pow_table()
    out = {}; why = collections.Counter()
    for k, pf in sorted(P.items()):
        params, body = heap.CORE[k]
        F = fns[k]
        ns = F.get('ns', k)
        G = S.get(ns) or S.get(k)
        if not straight(body): why['not straight'] += 1; continue
        if k in NZR: why['residual divisors'] += 1; continue
        code = F['code']
        jumps = [i for i, (op, a) in enumerate(code) if op == '.jump']
        if jumps != [len(code) - 1]: why['jumps'] += 1; continue
        oc, od, of = code[-1][1]
        st = F['stat'].get
        zero = st(oc) == ('k', 0, 0)
        nz = st(oc) is not None and st(oc)[0] == 'k' and (st(oc)[1], st(oc)[2]) != (0, 0)
        so = st(of)
        self_ = so == ('fpg', 0, 0) or (F['name'] == 'main' and so == ('k', 1, 0))
        t = pows.get(st(od)[1]) if st(od) is not None and st(od)[0] == 'k' and st(od)[2] == 0 else None
        fwd = nz and self_ and t is not None and F['entry'] + len(code) - 1 < t < F['entry'] + len(code)
        if (od, of) != (0, 1) or zero or fwd or not nz: why['return'] += 1; continue
        cells = promised(G, len(params))
        if cells is None: why['signature'] += 1; continue
        f = heap.Fn(k)
        stf = f.block([{}, {}, 0], f.body)
        post = []
        for c in cells:
            w = f.witness(stf[1], c)
            if w is None: break
            post.append((c, w))
        else:
            pre_ok = all(any(mono_cell(G, len(params), m) == c for m in G['pre']) for c in f.pre)
            if not pre_ok: why['precondition'] += 1; continue
            out[k] = dict(post=post, pre=list(f.pre), O=pf['O'], S=pf['S'], j=pf['j'], bpack=pf['bpack'])
            continue
        why['unwritten promise'] += 1
    if verbose:
        print('route', len(out), 'of', len(P), dict(why))
    return out


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
