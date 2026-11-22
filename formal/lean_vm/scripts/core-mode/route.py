"""The core route's first check (`formal/notes/core-mode.md`, `Guest/CoreMode/Core.lean`): the functions
passing `heapOk` and the pairing whose body is straight-line, whose only `JUMP` is its last
instruction, a return the pairing takes by its head statement, and whose signature its callers know
(`Mode.Sig`, `CoreMode/Sig/*.lean`) promises only frame cells, heap cells and runs of constant bounds over
its parameters (and returned products `retV`, each a returned value's monomial); each with the heap cells it promises (`CFun.post`) and their witnesses, the preconditions
the heap check then names (`HCert.sig.pre`), its pairing's oracle and stores. Which functions take the
route; the kernel's checks (`CoreMode.CoreOk`) confirm it.

`route()` returns `{name: dict(post=[(cell, wit)], pre=[cell], O=[..], S=[..], pack, bpack, j)}`, cells as
`(bases, off)`, bases `((value number, exponent), ...)`, witnesses `('ev', n)` or `('pre', k)`."""
import os, re, sys, glob, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import heap  # noqa: E402
import framelit as FL  # noqa: E402
from compiled import tokens, parse, split_top  # noqa: E402,F401

GUEST = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
FIELDS = 'pc entry self pre preR term ret post postR postL preP postP postLP retV postT postC'.split()


SIGS = None


def sigs():
    """Each function's `Mode.Sig`, by namespace name, fields parsed: what `sigc.py` writes (each function's
    contract, its rule file's or as written), whether or not it has run."""
    global SIGS
    if SIGS is not None:
        return SIGS
    import sigc, compiled
    lits, _ = sigc.signatures()
    fns = compiled.code()['fns']
    out = {}
    for n, text in lits.items():
        parts = split_top(text)
        assert len(parts) == 15, n
        out[fns[n]['ns']] = dict(pc=fns[n]['entry'], **{k: parse(v) for k, v in zip(FIELDS[1:], parts)})
    SIGS = out
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
        lits = [(blk.split('»', 1)[0], re.search(r'def frameFun : CoreMode.FFun :=\s*⟨(.*?)⟩\n\n', blk, re.S))
                for blk in t.split('\nnamespace LeanVM.Guest.Fn.«')[1:]]
        # a pack's walks in one section (`frame_gen.qual`)
        lits += [(m.group(1), m) for m in re.finditer(r'def Fn\.«([^»]+)»\.frameFun\s*:\s*CoreMode\.FFun\s*:=\s*⟨(.*?)⟩\n\n', t, re.S)]
        for n, m in lits:
            if m and split_top(m.group(m.lastindex))[7] != '.nil': out.add(n)
            if m and split_top(m.group(m.lastindex))[4] != '.nil': calls.add(n)
        # one `frame_fn%` a function (`framelit.py`)
        for n, d in FL.parse(t).items():
            if 'nzr' in d: out.add(n)
            if d.get('sigs', d['callees']): calls.add(n)
    return out, calls


def ptr_vals(body):
    """`CoreMode.ptrOf` over the statements, nested ones included: a `load`'s pointer, a hint's heap destination's."""
    out = []
    for s in body:
        if s[0] == 'a':
            a = s[1]
            if a[0] == 'load':
                out.append(a[2])
            elif a[0] == 'hint' and a[1][0] in ('witness', 'bits', 'bitsExp', 'digitsExp', 'windowsExp'):
                d = a[1][-1]
                if isinstance(d, tuple) and d and d[0] == 'heap':
                    out.append(d[1])
        elif s[0] == 'ite':
            out += ptr_vals(s[2]) + ptr_vals(s[3])
        elif s[0] == 'match':
            for arm in s[2]:
                out += ptr_vals(arm)
    return out


def route():
    import pair
    S = sigs()
    global NZR
    NZR, CALLS = frame_nzr()
    P, _ = pair.collect()
    AL = pair.AL
    fns = AL.functions()
    pows = AL.pow_table()
    out = {}
    for k, pf in sorted(P.items()):
        params, body = heap.CORE[k]
        if any(p in pf['extra'] for p in ptr_vals(body)):
            # `CoreMode.ptrCellB`: a dereferenced pointer at its certificate cell, no hint-only value
            continue  # hint-only pointer
        if pf.get('kind') in ('c', 'lc'):
            # a body with calls (`callc.py`) or a loop helper (`loopcc.py`), its
            # certificate by the check with calls
            out[k] = dict(post=[], pre=[], O=pf['O'], S=pf['S'], j=pf['j'], bpack=pf['bpack'], kind=pf['kind'])
            continue
        F = fns[k]
        ns = F.get('ns', k)
        G = S.get(ns) or S.get(k)
        if not branchy(body): continue  # not straight
        if not sel_ok(body, params): continue  # selector
        if k in CALLS: continue  # callees
        if F['name'] == 'main' or F['stat'].get(1) == ('fpg', 0, 0): continue  # main
        ex, locs = pf['extra'], pf['locs']
        loc = lambda v: ex[v] if v in ex else (locs[v] if v < len(locs) else 0)
        cells = promised(G, len(params), body, loc)
        if cells is None: continue  # signature
        f = heap.Fn(k)
        stf = f.block([{}, {}, 0], f.body)
        rets = [s[1] for s in body if s[0] == 'ret'][0]
        if not all(o < 2 ** 28 and o in G['ret'] and mono_cell(G, len(params), m) is not None and
                   any(f.mono(stf[0], v) == mono_cell(G, len(params), m) for v in rets) for o, m in G['retV']):
            continue  # returned product
        post = []
        for c in cells:
            w = f.witness(stf[1], subst(f, stf[0], c))
            if w is None: break
            post.append((c, w))
        else:
            pre_ok = all(any(mono_cell(G, len(params), m) == c for m in G['pre']) or c in run_points(G, len(params))
                         for c in f.pre)
            if not pre_ok: continue  # precondition
            out[k] = dict(post=post, pre=list(f.pre), O=pf['O'], S=pf['S'], j=pf['j'], bpack=pf['bpack'], kind='m1')
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
    """`route()` in a fresh interpreter, which leaves the caller's state as it was, its reads recorded as the caller's
    (`memo.follow`); computed once while what it reads is unchanged (`memo.py`)."""
    import memo
    return memo.cached('route', _route_sub)


def _route_sub():
    import subprocess
    r = subprocess.run([sys.executable, '-I', os.path.abspath(__file__), '--dump'], check=True, stdout=subprocess.PIPE,
                       text=True)
    R = json.loads(r.stdout)
    for r in R.values():
        r['post'] = [(_cell(c), tuple(w)) for c, w in r['post']]
        r['pre'] = [_cell(c) for c in r['pre']]
    return R


if __name__ == '__main__' and '--dump' in sys.argv:
    import memo
    memo.follow()
    out, sys.stdout = sys.stdout, open(os.devnull, 'w')
    json.dump(route(), out)
