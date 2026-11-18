"""The core route's functions with calls (`formal/notes/core-mode.md`, `CoreMode/Core.lean`'s `HeapK.c`): bodies of
atoms, calls and one return, checked by `heapOkC` with each callee's heap signature its mode signature's
(`Pack/*/ModeSig.lean`) translated (`CoreMode.fitB`: preconditions all of the mode signature's, guarantees some of
them), the function's own heap signature its own mode signature's translated (`CoreMode.sigOk`). The certificate's
witnesses come from `infer.py`'s pass (`heapOkC`'s format, no extra feature) run once at those signatures, which must
not grow.

`results()` returns `{name: dict(pass, sig, cs)}` for the functions whose certificate is complete, and the reasons of the
others. Usage (a census): python3 -I scripts/core-mode/callc.py [--fn NAME]"""
import os, sys, collections
ARGV = list(sys.argv)
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
    """Bodies of atoms, calls and conditional calls (at least one) and one final `ret`, not loop helpers."""
    out = []
    for k, (params, body) in sorted(CORE.items()):
        acc = kinds(body, collections.Counter())
        if set(acc) <= {'a', 'ret', 'call', 'callIf', 'dispatch'} and (acc['call'] or acc['callIf'] or acc['dispatch']) \
                and acc['ret'] == 1 and \
                body[-1][0] == 'ret' and k not in I.IS_LOOP:
            out.append(k)
    return out


class No(Exception):
    pass


def _em():
    """`emitc` (whose import takes `sys.argv` over), the caller's arguments kept."""
    saved = list(sys.argv)
    import emitc
    sys.argv[:] = saved
    return emitc


def cell(m, nslots, ent=None, G=None, ret_ok=None, gl=None):
    """A mode product `(fp, k, bs)` as a heap cell over slots (frame cell `2 + b` is slot `b`; with `gl`, the caller's
    cell `d` linked to slot `b` with no power of `g`, `CoreMode.baseOfL`), or `No`."""
    fp, k, bs = m
    if fp != 0:
        raise No('frame address')
    out = []
    for b, e in bs:
        if gl and b[0] == 'hp' and b[1] == 1 and b[2] in gl and gl[b[2]][1] == 0:
            out.append((gslot(gl[b[2]][0], nslots), e))
            continue
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


def bound(b, n, ent, gl=None):
    """`CoreMode.idxX`: a run bound as a heap index, a constant or an entry cell's exponent (`.val`); with `gl`
    (`CoreMode.idxL`), the exponent of the caller's cell `d` linked to slot `b` times `g^k`."""
    if gl and b[0] == 'ex' and b[1][0] == 'hp' and b[1][1] == 1 and b[2] == 0 and b[1][2] in gl:
        sl, k = gl[b[1][2]]
        return I.mk(((gslot(sl, n), 1),), k)
    if b[0] == 'num':
        if not b[1] < 2 ** 62:
            raise No('run bound')
        return I.num(b[1])
    if b[0] == 'ex' and b[1][0] == 'fr' and b[2] == 0:
        o = b[1][1]
        if not (2 <= o and o - 2 < n and o < 2 ** 28) or (ent is not None and not ent(o)):
            raise No('run bound slot')
        return I.base(o - 2)
    raise No('run bound')


def runX(r, n, ent=None, gl=None):
    """`CoreMode.rngX`: a run with exponent bounds (`CoreMode.rngL` with the caller's cells `gl` linked)."""
    q, lo, hi, S, d = r
    c = cell(q, n, ent, gl=gl)
    return (I.shift(c, d), S, bound(lo, n, ent, gl), bound(hi, n, ent, gl))


def gslot(b, n):
    """A linked slot as the inference's value: a parameter `b < n`, or ghost `b - n` (`GB + j`)."""
    return b if b < n else I.GB + (b - n)


_LINKS = {}


def gl_of(k):
    """`CFun.gl`, of `CoreMode.glOk`'s family: for a callee of `anyLink` (`Res/AnyData.lean`, its entries and bound
    parameters `pE`, `pL`), the caller's cell `2` linked to `pE` and cell `5` to `pL·g`; else none. As `{d: (b, k)}`."""
    if not _LINKS:
        import re
        t = open(os.path.join(GUEST, 'Res', 'AnyData.lean'), encoding='utf-8').read()
        for f, e, b in re.findall(r'\(name% «([^»]+)», (\d+), (\d+)\)', t):
            _LINKS[f] = {2: (int(e), 0), 5: (int(b), 1)}
        _LINKS.setdefault(None, None)
    if ml_k(k) is not None:
        # the ghost family (`CoreMode.mlGl`): the caller's cell `2` the one ghost slot, cell `5` the parameter `3`
        return {2: (len(CORE[k][0]), 0), 5: (3, 0)}
    return dict(_LINKS.get(k) or {}) if k not in I.IS_LOOP else {}


def ml_k(k):
    """`CoreMode.mlK`: `k` for `child_claim_list_mono_last__L{k}`, `1 ≤ k < 17`."""
    import re
    m = re.fullmatch(r'child_claim_list_mono_last__L(\d+)', k)
    return int(m.group(1)) if m and 1 <= int(m.group(1)) < 17 else None


def gl_lean(k):
    """`CFun.gl` as Lean."""
    return '[' + ', '.join('(%d, %d, %d)' % (d, b, kk) for d, (b, kk) in sorted(gl_of(k).items())) + ']'


def prun(p, n, ent=None, const=False):
    """`CoreMode.prunIs`: a pointer run, its offsets as they are."""
    return ((run if const else runX)(p[0], n, ent), tuple(p[1]))


def hp_of(m):
    """`CoreMode.hpOf`: a pointer-based product `g^k · [[q] · g^d]` as `(q, d, k)`."""
    fp, k, bs = m
    if fp == 0 and len(bs) == 1 and bs[0][1] == 1 and bs[0][0][0] == 'hp':
        return bs[0][0][1], bs[0][0][2], k
    return None


def hp_facts(ms, n, ent=None):
    """Pointer-based products as pointer facts `(⟨[(q - 2, 1)], d⟩, offsets)` (`CoreMode.hpIn`, `hpAll`)."""
    by = collections.defaultdict(set)
    for m in ms:
        q, d, k = hp_of(m)
        if not (2 <= q and q - 2 < n and q < 2 ** 28) or (ent is not None and not ent(q)):
            raise No('pointer base slot')
        by[(q, d)].add(k)
    return [(I.mk(((q - 2, 1),), d), tuple(sorted(ks))) for (q, d), ks in sorted(by.items())]


def callee_sig(G, na, nr):
    """`fitB`: the callee's heap signature at a call of `na` arguments and `nr` returned words; a loop's
    runs (`postL`, `postLP`) among its guarantees."""
    if G['self'] != ('id', 'none') and not (G['self'][0] == 'some' and G['self'][1] < 2 ** 28):
        raise No('callee self')
    if 0 not in G['entry'] or 1 not in G['entry']:
        raise No('callee header')
    h = I.Sig(na)
    ent = lambda o: o in G['entry']
    h.pre = [cell(m, na, ent) for m in G['pre'] if not hp_of(m)]
    h.preP = hp_facts([m for m in G['pre'] if hp_of(m)], na, ent)
    if any(c not in h.pre for c, _ in h.preP):
        raise No('callee pointer cell')
    h.preR = [runX(r, na, ent) for r in G['preR']]
    h.prePR = [prun(p, na, ent) for p in G['preP']]
    if any(p[0] not in h.preR for p in h.prePR):
        raise No('callee preP cells')
    for m in G['post']:
        try:
            if not hp_of(m):
                h.post.append(cell(m, na + nr))
        except No:
            pass
    try:
        h.postP = hp_facts([m for m in G['post'] if hp_of(m)], na + nr)
    except No:
        h.postP = []
    for r in G['postR'] + G['postL']:
        try:
            h.postR.append(runX(r, na + nr))
        except No:
            pass
    for p in G['postP'] + G['postLP']:
        try:
            h.postPR.append(prun(p, na + nr))
        except No:
            pass
    return h


def const_pow(body, v):
    """`CoreMode.constPow`: a value a top-level `const` atom before any `ret` sets to a power of `g` below `2^62`."""
    for s in body:
        if s[0] == 'ret':
            return False
        if s[0] == 'a' and s[1][0] == 'const' and s[1][1] == v:
            c = s[1][2]
            e = I.POWS.get(c[0]) if c[1] == 0 else None
            return e is not None and e < 2 ** 62
    return False


def own_sig(G, np, nr, gl=None):
    """`sigOk`: the function's heap signature, its mode signature's translated (its `preR` with the caller's cells
    `gl` linked, `CoreMode.rngLIs`)."""
    if G['self'] != ('id', 'none'):
        raise No('self')
    for f in ('term', 'postL', 'postLP', 'postT', 'postC'):
        if G[f]:
            raise No('own ' + f)
    h = I.Sig(np)
    h.pre = [cell(m, np) for m in G['pre'] if not hp_of(m)]
    h.preP = hp_facts([m for m in G['pre'] if hp_of(m)], np)
    def own_pre_run(r):
        try:
            return runX(r, np)
        except No:
            if not gl:
                raise
            return runX(r, np, gl=gl)
    h.preR = [own_pre_run(r) for r in G['preR']]
    # the ghost slots the links name (`CFun.gl` past the parameters)
    h.ghosts = [('link', d) for d, (b, _) in sorted((gl or {}).items()) if b >= np]
    h.prePR = [prun(p, np) for p in G['preP']]
    ret_ok = lambda o: (o - 2 < np and o in G['entry']) or (np <= o - 2 < np + nr and o in G['ret'])
    h.post = [cell(m, np + nr, ret_ok) for m in G['post'] if not hp_of(m)]
    h.postP = hp_facts([m for m in G['post'] if hp_of(m)], np, lambda q: q in G['entry'])
    if any(c not in h.post for c, _ in h.postP):
        raise No('own pointer cell')
    # bounds an entry run bounds too (`CoreMode.expCells`, `expB`): their cells' words have exponents (`ExpW`)
    expc = exp_cells(G)

    def own_run(r):
        try:
            return run(r, np + nr, ret_ok)
        except No:
            for b in (r[1], r[2]):
                if b[0] != 'num' and not (b[0] == 'ex' and b[1][0] == 'fr' and b[1][1] in expc and b[1][1] < 2 ** 28):
                    raise No('run bound')
            return runX(r, np + nr, ret_ok)
    h.postR = [own_run(r) for r in G['postR']]
    h.postPR = [(own_run(p[0]), tuple(p[1])) for p in G['postP']]
    # a pointer run's cells among the runs guaranteed (`sigOk`'s `postP` case asks both)
    h.postR += [p[0] for p in h.postPR if p[0] not in h.postR]
    h.retM = {}
    for o, m in G['retV']:
        if not (o < 2 ** 28 and o in G['ret'] and 2 + np <= o):
            raise No('retV')
        h.retM[o - 2 - np] = cell(m, np, lambda o2: o2 in G['entry'])
    return h


def exp_cells(G):
    """`CoreMode.expCells`: the frame cells the entry runs (`preR`, `preP`) bound by exponent."""
    return {b[1][1] for r in G['preR'] + [p[0] for p in G['preP']] for b in (r[1], r[2])
            if b[0] == 'ex' and b[1][0] == 'fr'}


def exp_bounds(h, args, body, np, expc):
    """`CoreMode.callsB`'s exponents (`idxPowC`): each bound `.val b` of the callee's runs an argument a top-level
    `const` sets to a power of `g`, or a parameter `k` whose cell `2 + k` an entry run bounds (`expArg`)."""
    for r in h.preR + [p[0] for p in h.prePR]:
        for b in (r[2], r[3]):
            if b[0]:
                (sl, _), = b[0]
                a = args[sl]
                if not (const_pow(body, a) or (a < np and 2 + a in expc)):
                    raise No('callee bound not a constant power')


def infer_one(k, S, allow=None, hcsig=None):
    """`hcsig`: callees whose contract is their own heap signature (`callhc.py`), by stable name: their signature
    as is (`CFun.hcs`), no translation."""
    EM = _em()
    params, body = CORE[k]
    np = len(params)
    rets = [s[1] for s in body if s[0] == 'ret'][0]
    G = S.get(k)
    if G is None:
        raise No('no mode signature')
    own = own_sig(G, np, len(rets), gl_of(k))
    cs = {}
    hcs = set()
    for s in body:
        if s[0] == 'call':
            calls = [(s[1], s[2], len(s[3]))]
        elif s[0] == 'callIf':
            calls = [(s[2], s[3], 0)]
        elif s[0] == 'dispatch':
            calls = [(f, s[3], len(s[4])) for f in s[2]]
        else:
            continue
        for f, args, nr in calls:
            Gf = S.get(STABLE.get(f, f)) or S.get(f)
            if Gf is None:
                raise No('callee without mode signature')
            if f == k:
                raise No('recursive')
            if hcsig and I.callee(f) in hcsig:
                h = hcsig[I.callee(f)].clone()
                hcs.add((f, len(args), nr))
            else:
                h = callee_sig(Gf, len(args), nr)
            exp_bounds(h, args, body, np, exp_cells(G))
            if f in cs and cs[f].key() != h.key():
                raise No('callee arity')
            cs[f] = h
    dsp = dsp_of(k, body)
    I.SIGS.clear()
    for f, h in cs.items():
        I.SIGS[I.callee(f)] = h
    G0 = own.clone()
    I.SIGS[k] = G0
    P = I.Pass(k, G0).run()
    if G0.pre != own.pre or G0.preR != own.preR or G0.prePR != own.prePR or G0.preP != own.preP:
        raise No('own precondition grows')
    # the witnesses: the emitter's solver, in `heapOkC`'s own pass, at these signatures
    sigs, hs = {}, {}
    for f, h in cs.items():
        dr = []
        hs[f] = sigs[I.callee(f)] = EM.sig_of(h, len(CORE[I.callee(f)][0]), dr)
        if dr:
            raise No('callee signature dropped')
    dr = []
    sigs[k] = EM.sig_of(own, np, dr)
    if dr:
        raise No('own signature dropped')
    sigOf = lambda g: sigs.get(I.callee(g), EM.C.EMPTY)
    H, Sv, pas = EM.solve(k, P, sigs, sigOf)
    if pas.fails or Sv.miss:
        raise No('unwitnessed: ' + str((list(pas.fails) + [('miss',) + m for m in Sv.miss])[0])[:60])
    if EM.check(k, H, sigOf) is not None:
        raise No('recheck')
    if H.res and not (allow and allow(k, H.res)):
        raise No('residuals')
    return dict(cert=H, cs=hs, dsp=dsp, hcs=sorted(hcs))


_FNS = {}


def dsp_of(k, body):
    """`CFun.dsp`: each dispatch's callees by its call site's callee frame cell (`callsB`: every site of a dispatch's
    arguments and returns lists that dispatch's callees)."""
    ds = [s for s in body if s[0] == 'dispatch']
    if not ds:
        return []
    if not _FNS:
        sys.path.insert(0, os.path.join(HERE, '..', 'bridge-cert'))
        import align
        _FNS.update(align.functions())
    sites = _FNS[k]['sites']
    out = {}
    for s in ds:
        qs = [q for q, si in sites.items() if si[0] == list(s[3]) and si[1] == list(s[4]) and si[4] != 0]
        if not qs:
            raise No('dispatch without site')
        for q in qs:
            if out.get(q, s[2]) != s[2]:
                raise No('dispatch sites clash')
            out[q] = s[2]
    for q, si in sites.items():
        for s in ds:
            if si[0] == list(s[3]) and si[1] == list(s[4]) and out.get(q, s[2]) != s[2]:
                raise No('dispatch sites clash')
    return sorted(out.items())


def results(verbose=False):
    I.F.clear()
    I.F.update({'ptr', 'pfr'})
    S = route.sigs()
    out, why = {}, collections.Counter()
    for k in candidates():
        try:
            out[k] = infer_one(k, S)
            out[k]['text'] = ldata(k, out[k])
        except No as e:
            why[str(e).split(':')[0]] += 1
            if verbose and '--why' in ARGV:
                print(k, e)
    # bodies closed only with residuals of families (`callcres.py`, `CoreMode/CoreRes.lean`)
    import callcres
    callcres.extend(out, why, S, verbose)
    # leaves whose contract is their own heap signature, their callers re-inferred (`callhc.py`)
    import callhc
    callhc.extend(out, why, S, verbose)
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



def lcsig(h):
    """A callee's heap signature as Lean, no auxiliary declaration."""
    EM = _em()
    ax = EM.Aux()
    t = EM.lsig(h, ax)
    if ax.defs:
        raise No('callee signature too long')
    return t


def hcsig_ref(k):
    """A heap-contract function's own heap signature (`Gen/HcSig.lean`)."""
    return f'CoreMode.HcSig.«{k}».sig'


def hcsig_file(R):
    """`Gen/HcSig.lean`: each heap-contract function's own heap signature, its auxiliary declarations first."""
    EM = _em()
    out = [HCSIG_HEADER]
    for k in sorted(k for k, r in R.items() if r.get('hc')):
        ax = EM.Aux()
        t = EM.lsig(R[k]['cert'].sig, ax)
        auxt = ''.join(f'/-- Part of `sig`. -/\n{d}\n' for d in ax.defs)
        out.append(f'\nnamespace LeanVM.Guest.CoreMode.HcSig.«{k}»\n\n@[expose] public section\n\n{auxt}'
                   f'/-- `{k}`: its own heap signature, its contract. -/\ndef sig : CoreMode.HSig := {t}\n\n'
                   f'end\nend LeanVM.Guest.CoreMode.HcSig.«{k}»\n')
    return ''.join(out)


HCSIG_HEADER = """/-
  LeanVM.Guest.CoreMode.Gen.HcSig

  Generated by `scripts/core-mode/callc.py --emit`; do not edit.
  The heap signatures of the functions whose contract is their own (`CFun.hc`), which their callers name.
-/

module

public import LeanVM.Guest.CoreMode.Defs

set_option maxRecDepth 100000
set_option linter.all false
"""


def ldata(k, r):
    """A function's certificate and its callees' signatures as Lean, its auxiliary declarations first."""
    EM = _em()
    aux, body = EM.lcert(r['cert'])
    if r.get('hc'):
        # its own signature the one its callers name (`Gen/HcSig.lean`)
        aux = [d for d in aux if not d.startswith('def sig_')]
        assert body.startswith('  sig := ')
        rest = body[body.index('\n  reads := '):]
        body = f'  sig := {hcsig_ref(k)}' + rest
    auxt = ''.join(f'/-- Part of `hcert`. -/\n{d}\n' for d in aux)
    hcf = {f for f, _, _ in r.get('hcs', [])}
    cs = ',\n    '.join(f'("{f}", {hcsig_ref(I.callee(f)) if f in hcf else lcsig(h)})' for f, h in sorted(r['cs'].items()))
    return (f'{auxt}/-- `{k}`: its heap certificate. -/\ndef hcert : CoreMode.HCert where\n{body}\n'
            f'/-- `{k}`: its callees\' heap signatures, their mode signatures\' translated. -/\n'
            f'def csigs : List (String × CoreMode.HSig) :=\n  [{cs}]\n' + (
                '/-- `%s`: each dispatch\'s callees by its call site\'s callee frame cell. -/\n'
                'def dsp : List (ℕ × List String) :=\n  [%s]\n' % (k, ', '.join(
                    '(%d, [%s])' % (q, ', '.join('"%s"' % f for f in fs)) for q, fs in r['dsp'])) if r.get('dsp') else '') +
            f'/-- `{k}`: its own contract its heap signature\'s (`CFun.hc`). -/\ndef hcFlag : Bool := {"true" if r.get("hc") else "false"}\n'
            f'/-- `{k}`: its callees whose contract is their heap signature\'s (`CFun.hcs`), with argument and return '
            f'counts. -/\ndef hcCallees : List (String × ℕ × ℕ) :=\n  [{", ".join(f'("{f}", {a}, {b})' for f, a, b in r.get("hcs", []))}]\n')


def emit(R, check):
    import heap
    po = heap.pack_of()
    packs = collections.defaultdict(list)
    for k in sorted(R):
        packs[po[k][0]].append(k)
    files = {}
    for pack, ks in sorted(packs.items()):
        out = [HEADER.format(pack=pack, first=ks[0], more=len(ks) - 1)]
        if any(R[k].get('hc') or R[k].get('hcs') for k in ks):
            out[0] = out[0].replace('public import LeanVM.Guest.CoreMode.Defs\n',
                                    'public import LeanVM.Guest.CoreMode.Defs\npublic import LeanVM.Guest.CoreMode.Gen.HcSig\n')
        for k in ks:
            out.append(f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n{R[k]["text"]}'
                       f'\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        files[os.path.join(GEN, pack, 'DataC.lean')] = ''.join(out)
    files[os.path.join(GEN, 'HcSig.lean')] = hcsig_file(R)
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
    if '--emit' in ARGV:
        R, _ = results(True)
        emit(R, '--check' in ARGV)
    elif '--fn' in ARGV:
        k = ARGV[ARGV.index('--fn') + 1]
        I.F.clear()
        I.F.update({'ptr', 'pfr'})
        try:
            r = infer_one(k, route.sigs())
            print('ok', k, ldata(k, r))
        except No as e:
            print('no', k, e)
    else:
        results(True)
