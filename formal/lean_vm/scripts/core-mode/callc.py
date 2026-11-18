"""The core route's functions with calls (`formal/notes/core-mode.md`, `CoreMode/Core.lean`'s `HeapK.c`): bodies of
atoms, calls and one return, checked by `heapOkC` with each callee's heap signature its mode signature's
(`Pack/*/ModeSig.lean`) translated (`CoreMode.fitB`: preconditions all of the mode signature's, guarantees some of
them), the function's own heap signature its own mode signature's translated (`CoreMode.sigOk`). The certificate's
witnesses come from `infer.py`'s pass (`heapOkC`'s format, no extra feature) run once at those signatures, which must
not grow.

`results()` returns `{name: dict(pass, sig, cs)}` for the functions whose certificate is complete, and the reasons of the
others. Usage (a census): python3 -I scripts/core-mode/callc.py [--fn NAME]"""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import infer as I  # noqa: E402
sys.modules.setdefault('infer', I)
import route  # noqa: E402

CORE, STABLE = I.CORE, I.STABLE


def kinds(body, acc):
    for s in body:
        acc[s[0]] += 1
        if s[0] == 'ite':
            kinds(s[2], acc); kinds(s[3], acc)
        if s[0] == 'match':
            for a in s[2]:
                kinds(a, acc)
    return acc


def candidates():
    """Bodies of atoms, calls (at least one) and one final `ret`, not loop helpers."""
    out = []
    for k, (params, body) in sorted(CORE.items()):
        acc = kinds(body, collections.Counter())
        if set(acc) <= {'a', 'ret', 'call'} and acc['call'] and acc['ret'] == 1 and body[-1][0] == 'ret' and \
                k not in I.IS_LOOP:
            out.append(k)
    return out


class No(Exception):
    pass


def cell(m, nslots, ent=None, G=None, ret_ok=None):
    """A mode product `(fp, k, bs)` as a heap cell over slots (frame cell `2 + b` is slot `b`), or `No`."""
    fp, k, bs = m
    if fp != 0:
        raise No('frame address')
    out = []
    for b, e in bs:
        if b[0] != 'fr':
            raise No('pointer base')
        o = b[1]
        if not (2 <= o and o - 2 < nslots and o < 2 ** 28):
            raise No('slot')
        if ent is not None and not ent(o):
            raise No('cell not written')
        out.append((o - 2, e))
    return I.mk(tuple(out), k)


def run(r, nslots, ent=None):
    q, lo, hi, S, d = r
    if lo[0] != 'num' or hi[0] != 'num':
        raise No('run bound')
    if not (lo[1] < 2 ** 62 and hi[1] < 2 ** 62):
        raise No('run bound')
    c = cell(q, nslots, ent)
    return (I.shift(c, d), S, I.num(lo[1]), I.num(hi[1]))


def callee_sig(G, na, nr):
    """`fitB`: the callee's heap signature at a call of `na` arguments and `nr` returned words."""
    if G['self'] != ('id', 'none'):
        raise No('callee self')
    if G['preP']:
        raise No('callee preP')
    if 0 not in G['entry'] or 1 not in G['entry']:
        raise No('callee header')
    h = I.Sig(na)
    ent = lambda o: o in G['entry']
    h.pre = [cell(m, na, ent) for m in G['pre']]
    h.preR = [run(r, na, ent) for r in G['preR']]
    for m in G['post']:
        try:
            h.post.append(cell(m, na + nr))
        except No:
            pass
    for r in G['postR']:
        try:
            h.postR.append(run(r, na + nr))
        except No:
            pass
    return h


def own_sig(G, np, nr):
    """`sigOk`: the function's heap signature, its mode signature's translated."""
    if G['self'] != ('id', 'none'):
        raise No('self')
    for f in ('term', 'postL', 'postP', 'postLP', 'postT', 'postC'):
        if G[f]:
            raise No('own ' + f)
    h = I.Sig(np)
    h.pre = [cell(m, np) for m in G['pre']]
    h.preR = [run(r, np) for r in G['preR']]
    ret_ok = lambda o: (o - 2 < np and o in G['entry']) or (np <= o - 2 < np + nr and o in G['ret'])
    h.post = [cell(m, np + nr, ret_ok) for m in G['post']]
    h.postR = [run(r, np + nr, ret_ok) for r in G['postR']]
    h.retM = {}
    for o, m in G['retV']:
        if not (o < 2 ** 28 and o in G['ret'] and 2 + np <= o):
            raise No('retV')
        h.retM[o - 2 - np] = cell(m, np, lambda o2: o2 in G['entry'])
    return h


def infer_one(k, S):
    params, body = CORE[k]
    np = len(params)
    rets = [s[1] for s in body if s[0] == 'ret'][0]
    G = S.get(k)
    if G is None:
        raise No('no mode signature')
    own = own_sig(G, np, len(rets))
    cs = {}
    for s in body:
        if s[0] != 'call':
            continue
        f = s[1]
        Gf = S.get(STABLE.get(f, f)) or S.get(f)
        if Gf is None:
            raise No('callee without mode signature')
        if f == k:
            raise No('recursive')
        h = callee_sig(Gf, len(s[2]), len(s[3]))
        if f in cs and cs[f].key() != h.key():
            raise No('callee arity')
        cs[f] = h
    I.SIGS.clear()
    for f, h in cs.items():
        I.SIGS[I.callee(f)] = h
    G0 = own.clone()
    I.SIGS[k] = G0
    P = I.Pass(k, G0).run()
    if G0.pre != own.pre or G0.preR != own.preR:
        raise No('own precondition grows')
    if P.unc:
        raise No('uncovered: ' + ','.join(sorted({u[0] for u in P.unc})))
    if I.misses(P):
        raise No('unwitnessed guarantee')
    for f, ws in P.calls:
        if any(w[0] == 'miss' or w[1] is None for _, w in ws):
            raise No('unwitnessed precondition')
    # own `retM`: each returned word's monomial at the `ret`
    for st, vs in P.rets:
        for j, c in own.retM.items():
            if j >= len(vs) or P.mono(st, vs[j]) != c:
                raise No('retM')
    if P.res:
        raise No('residuals')
    return dict(pass_=P, sig=own, cs=cs)


def results(verbose=False):
    I.F.clear()
    S = route.sigs()
    out, why = {}, collections.Counter()
    for k in candidates():
        try:
            out[k] = infer_one(k, S)
        except No as e:
            why[str(e).split(':')[0]] += 1
            if verbose and '--fn' in sys.argv:
                print(k, e)
    if verbose:
        print('calls: %d of %d candidates' % (len(out), len(candidates())), dict(why.most_common()))
    return out, why


# ---- the certificates in `heapOkC`'s format: `Gen/<pack>/DataC.lean`

GUEST = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
GEN = os.path.join(GUEST, 'CoreMode', 'Gen')
HEADER = """/-
  LeanVM.Guest.CoreMode.Gen.«{pack}».DataC

  Generated by `scripts/core-mode/callc.py --emit`; do not edit.
  The heap certificates of `{first}` and {more} more (bodies with calls), their callees' heap signatures.
-/

module

public import LeanVM.Guest.CoreMode.Defs

set_option maxRecDepth 100000
set_option linter.all false
"""



# ---- Lean text (the printing of `emitc.py` before its rewrite: witnesses from `infer.py`'s pass)

def lcell(c):
    if any(e < 0 for _, e in c[0]) or c[1] < 0:
        raise No('cell')
    return '⟨[' + ', '.join(f'({b}, {e})' for b, e in c[0]) + f'], {c[1]}⟩'


def lidx(i):
    """A signature run's bound: `.num n` or `.val slot`."""
    if not i[0]:
        if i[1] >= 2 ** 62 or i[1] < 0:
            raise No('idx')
        return f'(.num {i[1]})'
    if len(i[0]) == 1 and i[0][0][1] == 1 and i[1] == 0:
        return f'(.val {i[0][0][0]})'
    raise No('idx')


def lrun(r):
    Q, S, lo, hi = r
    return f'⟨{lcell(Q)}, {S}, {lidx(lo)}, {lidx(hi)}⟩'


def lwit(P, w):
    k = w[0]
    if k == 'ev':
        return f'.ev {w[1]}'
    if k == 'pre':
        return f'.pre {w[1]}'
    if k == 'run':
        rw = w[1]
        r = rw[1] if isinstance(rw, tuple) and rw[0] == 'preR' else (len(P.sig.preR) + rw if isinstance(rw, int) else None)
        if r is None:
            raise No('wit')
        return f'.run {r} [{", ".join(str(P.wren[i]) for i in w[2])}]'
    raise No('wit')


def wrap(items, ind='    ', width=110):
    lines, cur = [], ''
    for it in items:
        if cur and len(ind) + len(cur) + len(it) + 2 > width:
            lines.append(cur + ',')
            cur = ''
        cur = f'{cur}, {it}' if cur else it
    if cur:
        lines.append(cur)
    return ('\n' + ind).join(lines)


def lsig(G, ind='    '):
    f = []
    if G.pre:
        f.append(f'pre := [{wrap(map(lcell, G.pre), ind + "  ")}]')
    if G.post:
        f.append(f'post := [{wrap(map(lcell, G.post), ind + "  ")}]')
    if G.preR:
        f.append(f'preR := [{wrap(map(lrun, G.preR), ind + "  ")}]')
    if G.postR:
        f.append(f'postR := [{wrap(map(lrun, G.postR), ind + "  ")}]')
    if G.retM:
        f.append(f'retM := [{wrap((f"({j}, {lcell(c)})" for j, c in sorted(G.retM.items())), ind + "  ")}]')
    return '{ ' + (',\n' + ind + '  ').join(f) + ' }' if f else '{}'


def lcert(r):
    P = r['pass_']
    P.wren = {}
    by_d = collections.defaultdict(list)
    for (d, p, off), w in sorted(P.reads.items()):
        by_d[d].append(f'({p}, {off}, {lwit(P, w)})')
    reads = wrap(f'({d}, [{", ".join(rs)}])' for d, rs in sorted(by_d.items()))
    calls = wrap('[' + ', '.join(lwit(P, w) for _, w in ws) + ']' for f, ws in P.calls)
    rets = wrap('[' + ', '.join(lwit(P, w) for _, w in ws) + ']' for ws in P.ret_wits)
    return (f'  sig :=\n    {lsig(r["sig"])}\n  reads := [{reads}]\n  res := []\n  calls := [{calls}]\n'
            f'  rets := [{rets}]\n')


def emit(R, check):
    import heap
    po = heap.pack_of()
    packs = collections.defaultdict(list)
    for k in sorted(R):
        packs[po[k][0]].append(k)
    files = {}
    for pack, ks in sorted(packs.items()):
        out = [HEADER.format(pack=pack, first=ks[0], more=len(ks) - 1)]
        for k in ks:
            r = R[k]
            cs = ',\n    '.join(f'("{f}",\n      {lsig(h, "      ")})' for f, h in sorted(r['cs'].items()))
            out.append(f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n'
                       f'/-- `{k}`: its heap certificate. -/\ndef hcert : CoreMode.HCert where\n{lcert(r)}\n'
                       f'/-- `{k}`: its callees\' heap signatures, their mode signatures\' translated. -/\n'
                       f'def csigs : List (String × CoreMode.HSig) :=\n  [{cs}]\n\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        files[os.path.join(GEN, pack, 'DataC.lean')] = ''.join(out)
    import glob
    stale = []
    for path in sorted(set(glob.glob(os.path.join(GEN, '*', 'DataC.lean'))) - set(files)):
        stale.append(path)
        if not check:
            os.remove(path)
    for path, text in sorted(files.items()):
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if old != text:
            stale.append(path)
            if not check:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                open(path, 'w', encoding='utf-8').write(text)
    print('callc: %d functions, %d files, %d lines' % (len(R), len(files), sum(t.count('\n') for t in files.values())) +
          ((', stale: %d' % len(stale)) if check else ''))
    if check and stale:
        sys.exit(1)


if __name__ == '__main__':
    if '--emit' in sys.argv:
        R, _ = results(True)
        emit(R, '--check' in sys.argv)
    elif '--fn' in sys.argv:
        k = sys.argv[sys.argv.index('--fn') + 1]
        I.F.clear()
        try:
            r = infer_one(k, route.sigs())
            P = r['pass_']
            print('ok', k, 'reads', len(P.reads), 'calls', P.calls, 'rets', P.ret_wits)
        except No as e:
            print('no', k, e)
    else:
        results(True)
