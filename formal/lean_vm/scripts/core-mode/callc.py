"""The core route's functions with calls (`formal/notes/core-mode.md`, `CoreMode/Core.lean`'s `HeapK.c`): bodies of
atoms, calls and one return, checked by `heapOkC` with each callee's heap signature its mode signature's
(`CoreMode/Sig/*.lean`, `Fn.«k».csig`) translated (`CoreMode.fitB`: preconditions all of the mode signature's, guarantees some of
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
from pmap import pmap  # noqa: E402

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


def stmts_of(body):
    """`stmtsOf`: the statements of a body, nested ones included."""
    for s in body:
        yield s
        if s[0] == 'ite':
            yield from stmts_of(s[2])
            yield from stmts_of(s[3])
        elif s[0] == 'match':
            for a in s[2]:
                yield from stmts_of(a)


def top_ok(s):
    """A top-level statement `CoreMode.topOk` takes: a branch or `match` with no `ret` and no dispatch in it."""
    if s[0] not in ('ite', 'match'):
        return True
    acc = collections.Counter()
    for blk in (s[2], s[3]) if s[0] == 'ite' else s[2]:
        kinds(blk, acc)
    return not acc['ret'] and not acc['dispatch']


def candidates():
    """Bodies of atoms, branches, `match`es, calls and conditional calls (at least one) and one final `ret`, the
    branches with no `ret` or dispatch in them, not loop helpers."""
    out = []
    for k, (params, body) in sorted(CORE.items()):
        acc = kinds(body, collections.Counter())
        if set(acc) <= {'a', 'ret', 'call', 'callIf', 'dispatch', 'ite', 'match'} and \
                (acc['call'] or acc['callIf'] or acc['dispatch']) and acc['ret'] == 1 and \
                body[-1][0] == 'ret' and all(top_ok(s) for s in body) and k not in I.IS_LOOP:
            out.append(k)
    return out


class No(Exception):
    pass


def _em():
    """`emitc` (whose import takes `sys.argv` over), the caller's arguments kept."""
    saved = list(sys.argv)
    import emitc
    sys.argv[:] = saved
    emitc.WORD_RUN = True
    I.ARMRUN[0] = True
    I.DUPCALL[0] = True
    return emitc


def cell(m, nslots, ent=None, G=None, ret_ok=None, gl=None, gp=None):
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
        if gp and b[0] == 'hp' and b[1] != 1 and (b[1], b[2]) in gp:
            out.append((gslot(gp[(b[1], b[2])], nslots), e))
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
    if not max(0, hi[1] - lo[1]) < 2 ** 62:
        raise No('run bound')
    c = cell(q, nslots, ent)
    return norm_run((I.shift(c, d), S, I.num(lo[1]), I.num(hi[1])), c[1] + d)


def norm_run(R, off):
    """`CoreMode.rngC`'s normal form: a run of constant bounds `[a, b)` whose cell offset `off` is `2^62` or more
    (a negative one, modulo the order of `g`), or a bound `2^62` or more (past the order), starts at
    `(off + S·a) mod (2^64 - 1)` over `[0, b - a)`."""
    Q, S, lo, hi = R
    if lo[0] or hi[0] or (off < 2 ** 62 and lo[1] < 2 ** 62 and hi[1] < 2 ** 62):
        return R
    return ((Q[0], (off + S * lo[1]) % I.ORD), S, I.num(0), I.num(max(0, hi[1] - lo[1])))


def cov_runs(G, np):
    """`CoreMode.runCov`: stride-one runs `Q·g^o·[0, S·n)` whose strands `Q·g^(o+i)·[0, n)` of stride `S`, `i < S`, are
    runs of constant bounds of the mode signature's `preR`."""
    strands = set()
    for r in G['preR']:
        try:
            strands.add(run(r, np))
        except No:
            pass
    out = []
    for (Q, S, lo, hi) in sorted(strands):
        if S < 2 or lo != I.num(0) or not 0 < S * hi[1] < 2 ** 62:
            continue
        q = (Q, 1, I.num(0), I.num(S * hi[1]))
        if q not in out and all(((Q[0], Q[1] + i), S, lo, hi) in strands for i in range(S)):
            out.append(q)
    return out


def bound(b, n, ent, gl=None):
    """`CoreMode.idxX`: a run bound as a heap index, a constant or an entry cell's exponent plus a constant below
    `2^28` (`CoreMode.idxO`: `.val`, or the monomial `[b]·g^c`); with `gl` (`CoreMode.idxL`), the exponent of the
    caller's cell `d` linked to slot `b` times `g^k`."""
    if gl and b[0] == 'ex' and b[1][0] == 'hp' and b[1][1] == 1 and b[2] == 0 and b[1][2] in gl:
        sl, k = gl[b[1][2]]
        return I.mk(((gslot(sl, n), 1),), k)
    if b[0] == 'num':
        if not b[1] < 2 ** 62:
            raise No('run bound')
        return I.num(b[1])
    if b[0] == 'ex' and b[1][0] == 'fr' and b[2] < 2 ** 28:
        o = b[1][1]
        if not (2 <= o and o - 2 < n and o < 2 ** 28) or (ent is not None and not ent(o)):
            raise No('run bound slot')
        return I.mk(((o - 2, 1),), b[2])
    raise No('run bound')


def runX(r, n, ent=None, gl=None, gp=None):
    """`CoreMode.rngX`: a run with exponent bounds (`CoreMode.rngL` with the caller's cells `gl` linked, the argument
    words `gp` as ghost slots)."""
    q, lo, hi, S, d = r
    c = cell(q, n, ent, gl=gl, gp=gp)
    return norm_run((I.shift(c, d), S, bound(lo, n, ent, gl), bound(hi, n, ent, gl)), c[1] + d)


def gslot(b, n):
    """A linked slot as the inference's value: a parameter `b < n`, or ghost `b - n` (`GB + j`)."""
    return b if b < n else I.GB + (b - n)


_LINKS = {}


def gl_of(k):
    """`CFun.gl`, of `CoreMode.glOk`'s family: for a callee of `anyLink` (`CoreMode/Gen/AnyLink.lean`, its entries and bound
    parameters `pE`, `pL`), the caller's cell `2` linked to `pE` and cell `5` to `pL·g`; else none. As `{d: (b, k)}`."""
    if not _LINKS:
        import re
        t = open(os.path.join(GUEST, 'CoreMode', 'Gen', 'AnyLink.lean'), encoding='utf-8').read()
        for f, e, b in re.findall(r'\(name% «([^»]+)», (\d+), (\d+)\)', t):
            _LINKS[f] = {2: (int(e), 0), 5: (int(b), 1)}
        _LINKS.setdefault(None, None)
    if ml_k(k) is not None:
        # the ghost family (`CoreMode.mlGl`): the caller's cell `2` the one ghost slot, cell `5` the parameter `3`
        return {2: (len(CORE[k][0]), 0), 5: (3, 0)}
    import callcres
    if k in callcres.ST_LOOPS:
        # a stream-cursor loop (`CoreMode.stGl`, `loopGl`): the caller's cell `D` its first ghost slot, the caller's
        # frame address (`0`) its second
        np = len(CORE[k][0])
        return {callcres.ST_LOOPS[k][0]: (np, 0), 0: (np + 1, 0)}
    if k in I.IS_LOOP:
        if not _LINKS.get(k):
            return {}
        # a loop callee of `anyLink` (`CoreMode.alGl`): its links, then the caller's frame address its one ghost slot
        g = dict(_LINKS[k])
        g[0] = (len(CORE[k][0]), 0)
        return g
    return dict(_LINKS.get(k) or {})


def ml_k(k):
    """`CoreMode.mlK`: `k` for `child_claim_list_mono_last__L{k}`, `1 ≤ k < 17`."""
    import re
    m = re.fullmatch(r'child_claim_list_mono_last__L(\d+)', k)
    return int(m.group(1)) if m and 1 <= int(m.group(1)) < 17 else None


def gl_lean(k):
    """`CFun.gl` as Lean."""
    return '[' + ', '.join('(%d, %d, %d)' % (d, b, kk) for d, (b, kk) in gl_of(k).items()) + ']'


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


def hp1s(G):
    """The caller's cells `d` (bases `.hp 1 d`) among `hp_bs`."""
    return [d for q, d in hp_bs(G) if q == 1]


def hp_bs(G):
    """`CoreMode.hpBs`: the pointer bases `(q, d)` (`.hp q d`) of the entry runs' products, then of the entry products
    but pointer facts (`hpOf`), once each, in order."""
    out = []
    for bs in [r[0][2] for r in G['preR']] + [m[2] for m in G['pre'] if not hp_of(m)]:
        for b, _ in bs:
            if b[0] == 'hp' and (b[1], b[2]) not in out:
                out.append((b[1], b[2]))
    return out


def base_c1(G, na, ps, b):
    """`CoreMode.baseC1`: an argument's entry cell, or a pointer base of `ps` (past an argument's entry cell for
    `q ≠ 1`)."""
    if b[0] == 'fr':
        return 2 <= b[1] and b[1] - 2 < na and b[1] < 2 ** 28 and b[1] in G['entry']
    return (b[1], b[2]) in ps and (b[1] == 1 or (2 <= b[1] and b[1] - 2 < na and b[1] < 2 ** 28 and b[1] in G['entry']))


def callee_sig(G, na, nr):
    """`fitB`: the callee's heap signature at a call of `na` arguments and `nr` returned words; a loop's
    runs (`postL`, `postLP`) among its guarantees."""
    if G['self'] != ('id', 'none') and not (G['self'][0] == 'some' and G['self'][1] < 2 ** 28):
        raise No('callee self')
    if 0 not in G['entry'] or 1 not in G['entry']:
        raise No('callee header')
    h = I.Sig(na)
    ent = lambda o: o in G['entry']
    # the pointer bases its entry runs and products name, ghost slot `na + j` the `j`-th (`CoreMode.hpBs`): the
    # caller's cell `d` for `q = 1` (`glOfs`), the word at cell `d` past argument `q - 2`'s word otherwise (`gpOfs`)
    ps = hp_bs(G)
    gl = {d: (na + j, 0) for j, (q, d) in enumerate(ps) if q == 1}
    gp = {(q, d): na + j for j, (q, d) in enumerate(ps) if q != 1}
    gpre = []

    def pre_cell(m):
        try:
            return [cell(m, na, ent)]
        except No:
            # over pointer bases: a run of one point over the ghost slots (`fitB`, `baseC1`, `ptLIs`)
            if not ps or not all(base_c1(G, na, ps, b) for b, _ in m[2]):
                raise
            gpre.append((cell(m, na, ent, gl=gl, gp=gp), 1, I.num(0), I.num(1)))
            return []
    h.pre = [c for m in G['pre'] if not hp_of(m) for c in pre_cell(m)]
    h.preP = hp_facts([m for m in G['pre'] if hp_of(m)], na, ent)
    if any(c not in h.pre for c, _ in h.preP):
        raise No('callee pointer cell')
    # the word at an argument's cell, its cell a precondition (`fitB`)
    if any(q != 1 and I.mk(((q - 2, 1),), d) not in h.pre for q, d in ps):
        raise No('callee pointer base cell')

    def pre_run(r):
        try:
            return runX(r, na, ent)
        except No:
            # a run of constant bounds over argument entry cells and pointer bases (`fitB`, `baseC1`, `rngLIs`)
            if not ps or r[1][0] != 'num' or r[2][0] != 'num' or not all(base_c1(G, na, ps, b) for b, _ in r[0][2]):
                raise
            return runX(r, na, ent, gl=gl, gp=gp)
    h.preR = [pre_run(r) for r in G['preR']] + gpre
    h.ghosts = [('hp1', d) if q == 1 else ('hpw', q, d) for q, d in ps]
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
    # returned words' monomials over the argument cells its `retV` promises (`CoreMode.retMIn`)
    for o, m in G['retV']:
        k = o - 2 - na
        if 0 <= k < nr and o < 2 ** 28:
            try:
                h.retM[k] = cell(m, na)
            except No:
                pass
    return h


def const_pow(body, v, k=0):
    """`CoreMode.constPow`: a value a top-level `const` atom before any `ret` sets to a power of `g` below `2^62`; with
    `k`, the power times `g^k` (`CoreMode.idxPow`'s `.mono` case)."""
    for s in body:
        if s[0] == 'ret':
            return False
        if s[0] == 'a' and s[1][0] == 'const' and s[1][1] == v:
            c = s[1][2]
            e = I.POWS.get(c[0]) if c[1] == 0 else None
            return e is not None and e + k < 2 ** 62
    return False


JT_RUN = [None]


def jt_run():
    """The jump table's cells `[jtLo, jtHi)` as a run (`Mode.jtRng`; `sigOk` takes it among the own preconditions)."""
    import importlib.util
    spec = importlib.util.spec_from_file_location('compiled', os.path.join(HERE, 'compiled.py'))
    md = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(md)
    jt = md.load()['jt']
    return (((), 0), 1, ((), min(jt)), ((), max(jt) + 1))


def own_sig(G, np, nr, gl=None):
    """`sigOk`: the function's heap signature, its mode signature's translated (its `preR` with the caller's cells
    `gl` linked, `CoreMode.rngLIs`)."""
    if G['self'] != ('id', 'none'):
        raise No('self')
    for f in ('term', 'postL', 'postLP', 'postT', 'postC'):
        if G[f]:
            raise No('own ' + f)
    h = I.Sig(np)
    # own parameter words (`HSig.gw`): ghost slot `j` the word at `[p]·g^d`, `p` a parameter (`CoreMode.baseOfG`)
    h.gw, gwk = [], {}

    def ghost_b(q, d):
        if (q - 2, d) not in gwk:
            gwk[(q - 2, d)] = len(gwk)
            h.gw.append(((((q - 2, 1),), d), gwk[(q - 2, d)]))
        return I.GB + gwk[(q - 2, d)]

    def own_pre(m):
        try:
            return [cell(m, np)]
        except No as e:
            if str(e) != 'pointer base' or gl:
                raise
        fp, k, bs = m
        out = []
        for b, e in bs:
            if b[0] == 'fr' and 2 <= b[1] and b[1] - 2 < np and b[1] in G['entry'] and b[1] < 2 ** 28:
                out.append((b[1] - 2, e))
            elif b[0] == 'hp' and 2 <= b[1] and b[1] - 2 < np and b[1] in G['entry'] and b[1] < 2 ** 28:
                out.append((ghost_b(b[1], b[2]), e))
            else:
                raise No('pointer base')
        # over ghost slots: a run of one point (`HSig.pre` is over the parameters, `preOver`)
        gpre.append((I.mk(tuple(out), k), 1, I.num(0), I.num(1)))
        return []
    gpre = []
    h.pre = [c for m in G['pre'] if not hp_of(m) for c in own_pre(m)]
    h.preP = hp_facts([m for m in G['pre'] if hp_of(m)], np)
    def own_pre_run(r):
        try:
            return runX(r, np)
        except No:
            if not gl:
                raise
            return runX(r, np, gl=gl)
    h.preR = [own_pre_run(r) for r in G['preR']]
    h.preR += [q for q in cov_runs(G, np) if q not in h.preR]
    h.preR += [q for q in gpre if q not in h.preR]
    # the ghost slots the links name (`CFun.gl` past the parameters)
    h.ghosts = [('link', d) for d, (b, _) in sorted((gl or {}).items()) if b >= np] + \
        [('gw', key) for key, _ in sorted(gwk.items(), key=lambda p: p[1])]
    h.prePR = [prun(p, np) for p in G['preP']]
    ret_ok = lambda o: (o - 2 < np and o in G['entry']) or (np <= o - 2 < np + nr and o in G['ret'])
    # guarantees over the body's values (`CoreMode.postNIn`, `postRNIn`): products of parameters' words and of words a
    # top-level `load` reads past a parameter's (`baseOfP`), over the slots of `nv` (`CCell.mapN`)
    body0 = CORE_BODY.get('body') or []
    h.nv, h.postN, h.postRN = [], [], []

    def nslot(v):
        if v not in h.nv:
            h.nv.append(v)
        return h.nv.index(v)

    rlocs = (I.D['comp'].get(CORE_BODY.get('k')) or {}).get('locs') or []
    rvals = next((s[1] for s in body0 if s[0] == 'ret'), [])

    def base_p(b, e):
        if b[0] == 'fr' and 2 <= b[1] and b[1] - 2 < np:
            return (b[1] - 2, e)
        if b[0] == 'fr':
            # a return cell's returned value (`CoreMode.retAtCell`)
            v = next((v for v in rvals if v < len(rlocs) and rlocs[v] == b[1]), None)
            return None if v is None else (v, e)
        if b[0] == 'hp' and 2 <= b[1] and b[1] - 2 < np:
            n = hp_val(body0, b[1] - 2, b[2])
            return None if n is None else (n, e)
        return None

    def mono_okp(bs):
        return all(b[1] < 2 ** 28 and ((b[1] in G['entry'] and 2 <= b[1] and b[1] - 2 < np) or b[1] in G['ret'])
                   if b[0] == 'fr' else
                   (b[1] in G['entry'] and 2 <= b[1] and b[1] - 2 < np and b[1] < 2 ** 28) for b, _ in bs)

    def val_cell(m):
        fp, k, bs = m
        cb = [base_p(b, e) for b, e in bs]
        if fp != 0 or None in cb or not mono_okp(bs):
            raise No('post over values')
        return (tuple(cb), k)

    def post_n(m):
        c = val_cell(m)
        c = (tuple((nslot(v), e) for v, e in c[0]), c[1])
        if c not in h.postN:
            h.postN.append(c)

    def post(m):
        try:
            return [cell(m, np + nr, ret_ok)]
        except No:
            post_n(m)
            return []
    h.post = [c for m in G['post'] if not hp_of(m) for c in post(m)]
    h.postP = hp_facts([m for m in G['post'] if hp_of(m)], np, lambda q: q in G['entry'])
    if any(c not in h.post for c, _ in h.postP):
        raise No('own pointer cell')
    # bounds an entry run bounds too (`CoreMode.expCells`, `expB`): their cells' words have exponents (`ExpW`)
    expc = exp_cells(G)

    import callcres
    body = CORE_BODY.get('body') or []
    sels = dict(top_sels(body))
    tops = callcres.top_atoms(body)
    for x in range(np):
        if x not in sels and callcres.rc_bound(tops, x) is not None:
            sels[x] = callcres.rc_bound(tops, x)
    # a parameter of an exponent fact (`CoreMode.resQ`'s `expQ`)
    for x in range(np):
        if x not in sels and CORE_BODY.get('k') is not None and callcres.expq_bound(CORE_BODY['k'], x) is not None:
            sels[x] = callcres.expq_bound(CORE_BODY['k'], x)
    h.expRes = set()

    def own_run(r):
        try:
            return run(r, np + nr, ret_ok)
        except No:
            for b in (r[1], r[2]):
                if b[0] == 'num' or (b[0] == 'ex' and b[1][0] == 'fr' and b[1][1] < 2 ** 28 and
                                     ((b[2] == 0 and b[1][1] in expc))):
                    continue
                # a parameter bounded by its selector's `sel` residual, or by its range check's `rc` residual, with room
                # for the offset (`CoreMode.expRes`)
                if b[0] == 'ex' and b[1][0] == 'fr' and b[1][1] < 2 ** 28 and 2 <= b[1][1] and \
                        b[1][1] - 2 < np and sels.get(b[1][1] - 2) is not None and \
                        sels[b[1][1] - 2] + b[2] <= 2 ** 62:
                    h.expRes.add((b[1][1] - 2, sels[b[1][1] - 2]))
                    continue
                raise No('run bound')
            return runX(r, np + nr, ret_ok)
    def hp_cover(r):
        # a run up to the word at a parameter's `[p]·g^d` (`.hp q d`) plus `c`, inside a guaranteed run of the same
        # base and lower bound up to a constant `N`, the word loaded by a top-level `load` with an exponent fact
        # `e < m`, `m + c <= N + 1` (`CoreMode.postRB`)
        q, lo, hi, S, d = r
        if hi[0] != 'ex' or hi[1][0] != 'hp' or not 2 <= hi[1][1] or hi[1][1] - 2 >= np or k_own is None:
            return False
        tops = callcres.top_atoms(body)
        vs = [a[1] for a in tops if a[0] == 'load' and a[2] == hi[1][1] - 2 and a[3] == hi[1][2]]
        if not vs:
            return False
        m = callcres.expq_bound(k_own, vs[0])
        if m is None:
            return False
        for r2 in G['postR']:
            if r2[0] == q and r2[1] == lo and r2[3] == S and r2[4] == d and r2[2][0] == 'num' and \
                    m + hi[2] <= r2[2][1] + 1 and r2[2][1] < 2 ** 62:
                h.expRes.add((vs[0], m))
                return True
        return False
    k_own = CORE_BODY.get('k')

    def idx_n(b):
        # `CoreMode.idxN`, its value's exponent bounded by a residual (`idxOkN`): an exponent fact, a range check, a
        # selector
        if b[0] == 'num' and b[1] < 2 ** 62:
            return ('num', b[1])
        if b[0] == 'ex' and b[2] == 0:
            p = base_p(b[1], 1)
            if p is not None:
                v = p[0]
                m = callcres.expq_bound(k_own, v) if k_own is not None else None
                if m is None:
                    m = callcres.rc_bound(callcres.top_atoms(body0), v)
                if m is None:
                    m = dict(top_sels(body0)).get(v)
                if m is not None and m <= 2 ** 62:
                    h.expRes.add((v, m))
                    return ('val', v)
        raise No('run bound over values')

    def own_run_n(r):
        try:
            return [own_run(r)]
        except No:
            q, lo, hi, S, d = r
            if not mono_okp(list(q[2]) + [(b[1], 1) for b in (lo, hi) if b[0] == "ex"]):
                raise
            c = val_cell(q)
            lo2, hi2 = idx_n(lo), idx_n(hi)
            ix = lambda i: ('val', nslot(i[1])) if i[0] == 'val' else i
            run = (tuple((nslot(v), e) for v, e in c[0]), c[1] + d), S, ix(lo2), ix(hi2)
            if run not in h.postRN:
                h.postRN.append(run)
            return []
    h.postR = [x for r in G['postR'] if not hp_cover(r) for x in own_run_n(r)]
    h.postPR = [(own_run(p[0]), tuple(p[1])) for p in G['postP']]
    # a pointer run's cells among the runs guaranteed (`sigOk`'s `postP` case asks both)
    h.postR += [p[0] for p in h.postPR if p[0] not in h.postR]
    h.retM = {}
    for o, m in G['retV']:
        if not (o < 2 ** 28 and o in G['ret'] and 2 + np <= o):
            raise No('retV')
        h.retM[o - 2 - np] = cell(m, np, lambda o2: o2 in G['entry'])
    if CORE_BODY.get('k') == 'main':
        # `main`'s entry cells, its frame `0`: the constant cells `g^o` (`CoreMode.mainPre`)
        h.pre = list(h.pre) + [((), o) for o in G['entry'] if ((), o) not in h.pre]
    if 'jt' in I.F:
        # the jump table's cells, which every frame's entry has written (`entryAbs`)
        if JT_RUN[0] is None:
            JT_RUN[0] = jt_run()
        h.preR = list(h.preR) + [JT_RUN[0]]
    return h


CORE_BODY = {}


def hp_val(body, k, d):
    """`CoreMode.hpVal`: the value a top-level `load` reads at parameter `k`'s `[p]·g^d`, before the first `ret`."""
    for s in body:
        if s[0] == 'ret':
            return None
        if s[0] == 'a' and s[1][0] == 'load' and s[1][2] == k and s[1][3] == d:
            return s[1][1]
    return None


def def_of(body, n):
    """`CoreMode.defOf`: the first top-level `const`, `copy` or `mul` defining `n`, before any `ret`."""
    for s in body:
        if s[0] == 'ret':
            return None
        if s[0] == 'a' and s[1][0] in ('const', 'copy', 'mul') and s[1][1] == n:
            return s[1]
    return None


WORD_FUEL = 4


def word_nf(body, k, n):
    """`CoreMode.wordNf`: a value's word as a monomial through the top-level atoms, `k` deep."""
    import heapc
    self_ = (((n, 1),), 0)
    if k == 0:
        return self_
    a = def_of(body, n)
    if a is None:
        return self_
    if a[0] == 'const':
        c = a[2]
        if c[1] != 0:
            return self_
        e = 0 if c[0] == 1 else I.POWS.get(c[0])
        return ((), e) if e is not None else self_
    if a[0] == 'copy':
        return word_nf(body, k - 1, a[2])
    return heapc.cmul(word_nf(body, k - 1, a[2]), word_nf(body, k - 1, a[3]))


def ghost_w(body, ks, p):
    """`CoreMode.ghostW`: a callee's ghost word at a call on the argument values `ks`, of its pointer base `p`."""
    q, d = p
    if q == 1:
        return (((d - 2, 1),), 0)
    if q - 2 >= len(ks):
        return None
    n = hp_val(body, ks[q - 2], d)
    return word_nf(body, WORD_FUEL, n) if n is not None else None


def top_sels(body):
    """`Res.topSels`: the top-level selectors (a `match`'s or `dispatch`'s value and arm count) up to the first statement
    that may return."""
    import callcres
    out = []
    for s in body:
        if s[0] in ('match', 'dispatch'):
            out.append((s[1], len(s[2])))
        if callcres.has_ret(s):
            break
    return out


def exp_cells(G):
    """`CoreMode.expCells`: the frame cells the entry runs (`preR`, `preP`) bound by exponent."""
    return {b[1][1] for r in G['preR'] + [p[0] for p in G['preP']] for b in (r[1], r[2])
            if b[0] == 'ex' and b[1][0] == 'fr'}


def exp_bounds(h, args, body, np, expc, k=None, acc=None):
    """`CoreMode.callsB`'s exponents (`idxPowC`): each bound `.val b` of the callee's runs an argument a top-level
    `const` sets to a power of `g`, a parameter `k` whose cell `2 + k` an entry run bounds (`expArg`), or an argument
    of an exponent fact or range checked, its residual `e(a) < m` added to `acc` (`resArg`)."""
    for r in h.preR + [p[0] for p in h.prePR]:
        for b in (r[2], r[3]):
            if b[0]:
                (sl, _), = b[0]
                a = args[sl]
                if const_pow(body, a, b[1]) or (b[1] == 0 and a < np and 2 + a in expc):
                    continue
                import callcres
                B = callcres.expq_bound(k, a) if k is not None and b[1] == 0 else None
                if B is None and b[1] == 0:
                    B = (callcres.addr_bound(k, a) if k is not None else None) or \
                        callcres.rc_bound(callcres.top_atoms(body), a)
                if B is None and b[1] > 0 and k is not None:
                    # an argument times `g^c`, its bound plus `c` an exponent (`CoreMode.resArg`'s `.mono`)
                    B = callcres.vs_bound(k, a)
                    if B is not None and not B + b[1] < 2 ** 62:
                        B = None
                if B is None or acc is None:
                    raise No('callee bound not a constant power')
                acc.add((a, B))


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
    CORE_BODY['body'] = body
    CORE_BODY['k'] = k
    own = own_sig(G, np, len(rets), gl_of(k))
    if own.gw and gl_of(k):
        # own parameter words (`HSig.gw`) as the ghost slots only where no caller's cell is linked (`CoreMode.gwSlots`)
        raise No('own parameter words and links')
    cs = {}
    hcs = set()
    arg_res = set()
    for s in stmts_of(body):
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
            for a in h.ghosts:
                # the caller's cells, its own parameters' entry cells; the words at an argument's cells, values a
                # top-level `load` names (`CoreMode.hpArgOk`)
                if a[0] == 'hp1' and not (2 <= a[1] and a[1] - 2 < np and a[1] < 2 ** 28 and a[1] in G['entry']):
                    raise No('callee caller cell')
                if a[0] == 'hpw' and hp_val(body, args[a[1] - 2], a[2]) is None:
                    raise No('callee argument word')
            exp_bounds(h, args, body, np, exp_cells(G), k, arg_res)
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
    # (the inference may want more own preconditions than the signature states: the solver below, at `own`, decides)
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
    if (pas.fails or Sv.miss) and has_fa(body) and fa_past(k):
        # with frame run cells past their runs, which the frame walk has written at the returns (`CoreMode.FAW`)
        EM.C.FA_EXTRA[k] = fa_past(k)
        H, Sv, pas = EM.solve(k, P, sigs, sigOf)
    if pas.fails or Sv.miss:
        raise No('unwitnessed: ' + str((list(pas.fails) + [('miss',) + m for m in Sv.miss])[0])[:60])
    # the callees' ghost words, those `hpArgOk` names
    for g, ks, ms in H.gargs:
        Gf = S.get(STABLE.get(g, g)) or S.get(g)
        if Gf is not None and not any(f == g for f, _, _ in hcs) and \
                [tuple(m) if m is not None else None for m in ms] != [ghost_w(body, ks, p) for p in hp_bs(Gf)]:
            raise No('callee ghost words')
    # the selectors' `sel` residuals giving the own guarantees' bounds exponents (`CoreMode.expI`'s `expRes`)
    for x, m in sorted(own.expRes):
        r = ('lt', ('val', x), ('num', m))
        if r not in H.res:
            H.res.append(r)
    # the arguments' exponent facts giving the callees' run bounds exponents (`CoreMode.resArg`)
    for x, m in sorted(arg_res):
        r = ('lt', ('val', x), ('num', m))
        if r not in H.res:
            H.res.append(r)
    if EM.check(k, H, sigOf) is not None:
        raise No('recheck')
    if H.res and not (allow and allow(k, H.res)):
        raise No('residuals')
    hk = sigs[k]
    if has_fa(body) and (hk.post or hk.postR or hk.postP or hk.postPR or hk.postQ or hk.postN or hk.postRN):
        # guarantees met without the frame run cells (`HCert.fas` empty) if they can; else the frame run cells
        # written at the returns (`CoreMode.faNeed`, `faRetOk`, which the kernel checks on the frame walk)
        fas = H.fas
        H.fas = []
        if EM.check(k, H, sigOf) is not None:
            H.fas = fas
    return dict(cert=H, cs=hs, dsp=dsp, hcs=sorted(hcs))


FA_PAST = {}


def fa_past(k):
    """The frame walk's cells past `k`'s top-level frame runs written at every return (`fa_past.py`, which needs
    `MODE_CERT_CACHE`), as `(kp, i)`; none without it."""
    if k in FA_PAST:
        return FA_PAST[k]
    FA_PAST[k] = []
    if not os.environ.get('MODE_CERT_CACHE'):
        return []
    import subprocess, json, heapc
    body = CORE[k][1]
    locs = I.D['comp'][k]['locs']
    fas = []
    for s in body:
        if not heapc._noret(s):
            break
        if s[0] == 'a' and s[1][0] == 'frameAddr' and s[1][2] and s[1][2][0] < len(locs):
            fas.append([s[1][1], locs[s[1][2][0]], len(s[1][2])])
    if fas:
        r = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'fa_past.py')], input=json.dumps({k: fas}),
                           capture_output=True, text=True, check=True)
        FA_PAST[k] = [tuple(p) for p in json.loads(r.stdout).get(k, [])]
    return FA_PAST[k]


def has_fa(body):
    """Not `CoreMode.noFA`: a `frameAddr` atom anywhere in the body (then `CoreOk.faret` checks the frame run cells
    the guarantees take at the returns, `CoreMode.faNeed`)."""
    for s in body:
        if s[0] == 'a' and s[1][0] == 'frameAddr':
            return True
        if s[0] == 'ite' and (has_fa(s[2]) or has_fa(s[3])):
            return True
        if s[0] == 'match' and any(has_fa(a) for a in s[2]):
            return True
    return False


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
    """`_results`, computed once while its inputs are unchanged (`memo.py`)."""
    import memo
    return memo.cached('callc.results', lambda: _results(verbose))


def _results(verbose=False):
    I.F.clear()
    I.F.update({'ptr', 'pfr'})
    S = route.sigs()
    out, why = {}, collections.Counter()

    def one(k):
        try:
            r = infer_one(k, S)
            r['text'] = ldata(k, r)
            return r, None
        except No as e:
            return None, e
    cs = candidates()
    # each candidate on its own, in worker processes (`pmap.py`)
    for k, (r, e) in zip(cs, pmap(one, cs)):
        if e is None:
            out[k] = r
        else:
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
    """A function's own heap signature where its callers name it (`Gen/<pack>/Sig.lean`): a heap-contract
    function's, or one its callers' signatures equal (`sig_shared`)."""
    return f'CoreMode.HcSig.«{k}».sig'


def self_sig(r):
    """A function's own heap signature as Lean, if it needs no auxiliary declaration (as a callee's copy)."""
    try:
        return lcsig(r['cert'].sig)
    except No:
        return None


def sig_shared(R):
    """The callees' signatures stated once (`Gen/<pack>/Sig.lean`) and named by their callers' `csigs`: `(shared,
    refs)`, `shared` the functions whose own heap signature some caller's copy equals (their certificates name it
    too), `refs` each callee's name for its copy (a callee's copy is the same in every caller): its own signature
    (`sig`), or for a copy in two callers or more, the copy (`csig`)."""
    own = {k: self_sig(r) for k, r in R.items()}
    copies = collections.defaultdict(collections.Counter)
    for k, r in R.items():
        hcf = {f for f, _, _ in r.get('hcs', [])}
        for f, h in r['cs'].items():
            if f not in hcf:
                copies[I.callee(f)][lcsig(h)] += 1
    shared, refs = set(), {}
    for c, cnt in copies.items():
        for t, n in cnt.items():
            if c in R and own[c] == t:
                shared.add(c)
                refs[(c, t)] = hcsig_ref(c)
            elif n >= 2:
                refs[(c, t)] = f'CoreMode.HcSig.«{c}».csig' if len(cnt) == 1 else None
    return shared, {ct: n for ct, n in refs.items() if n}


def in_sigs(k, r, shared):
    """Whether `k`'s own heap signature is in its pack's signature module."""
    return bool(r.get('hc')) or k in shared


def sig_file(pack, ks, R, copies):
    """`Gen/<pack>/Sig.lean`: the own heap signatures of the pack's functions `ks` that their callers name, each
    with its auxiliary declarations, and the callees' copies `copies` (`[(callee, text)]`) that callers share."""
    EM = _em()
    out = [SIG_HEADER.format(pack=pack)]
    names = sorted(set(ks) | {c for c, _ in copies})
    cp = dict(copies)
    for k in names:
        if k in ks:
            ax = EM.Aux()
            t = EM.lsig(R[k]['cert'].sig, ax)
            out += [d.replace('def ', f'def «{k}».', 1) for d in ax.defs] + [f'def «{k}».sig : CoreMode.HSig := {t}\n']
        if k in cp:
            out.append(f'def «{k}».csig : CoreMode.HSig := {cp[k]}\n')
    out.append('\nend\nend LeanVM.Guest.CoreMode.HcSig\n')
    return ''.join(out)


SIG_HEADER = """/-
  LeanVM.Guest.CoreMode.Gen.«{pack}».Sig

  Generated by `scripts/core-mode/callc.py --emit`; do not edit.
  The heap signatures of the pack's functions that their callers name: `«f».sig`, `f`'s own, its contract
  (`CFun.hc`) or what its callers' copies (`csigs`) equal; `«f».csig`, the copy two callers or more hold.
-/

module

public import LeanVM.Guest.CoreMode.Defs

set_option maxRecDepth 100000
set_option linter.all false

namespace LeanVM.Guest.CoreMode.HcSig

@[expose] public section

"""


def ldata(k, r, shared=frozenset(), sigs=None, refs={}):
    """A function's certificate and its callees' signatures as Lean, its auxiliary declarations first. `shared`,
    `refs`: `sig_shared`'s; `sigs` (if given) collects the functions whose signature module the text names."""
    EM = _em()
    aux, body = EM.lcert(r['cert'])
    used = set()
    if in_sigs(k, r, shared):
        # its own signature the one its callers name (`Gen/<pack>/Sig.lean`)
        aux = [d for d in aux if not d.startswith('def sig_')]
        assert body.startswith('  sig := ')
        rest = body[body.index('\n  reads := '):]
        body = f'  sig := {hcsig_ref(k)}' + rest
        used.add(k)
    auxt = ''.join(f'{d}\n' for d in aux)
    hcf = {f for f, _, _ in r.get('hcs', [])}

    def entry(f, h):
        c = I.callee(f)
        if f in hcf:
            used.add(c)
            return hcsig_ref(c)
        t = lcsig(h)
        if (c, t) in refs:
            used.add(c)
            return refs[(c, t)]
        return t
    cs = ',\n    '.join(f'("{f}", {entry(f, h)})' for f, h in sorted(r['cs'].items()))
    if sigs is not None:
        sigs |= used
    return (f'{auxt}def hcert : CoreMode.HCert where\n{body}\n'
            f'def csigs : List (String × CoreMode.HSig) :=\n  [{cs}]\n' + (
                'def dsp : List (ℕ × List String) :=\n  [%s]\n' % (', '.join(
                    '(%d, [%s])' % (q, ', '.join('"%s"' % f for f in fs)) for q, fs in r['dsp'])) if r.get('dsp') else '') +
            f'def hcFlag : Bool := {"true" if r.get("hc") else "false"}\n'
            f'def hcCallees : List (String × ℕ × ℕ) :=\n  [{", ".join(f'("{f}", {a}, {b})' for f, a, b in r.get("hcs", []))}]\n')


GENW = os.path.join(GUEST, 'CoreMode', 'GenW')


def windows(R, po, shared=frozenset()):
    """The heap checks estimated past `heapwin.BUDGET` (the heartbeats, or the memory a module may take), in windows
    (`heapwin.one`): `GenW/<fn>/`, its `Ok.lean` stating `Fn.«fn».heap_okW` at the callees' signatures `csigs` as
    `CFun.sigOf` reads them, which `core.py`'s `heap_okC` takes. `({path: text}, {directory})`."""
    import heapwin
    epo = heapwin.E.pack_of()
    files, dirs = {}, set()
    for k in sorted(R):
        H = R[k]['cert']
        sigs = {I.callee(f): h for f, h in R[k]['cs'].items()}
        sigOf = lambda g, sigs=sigs: sigs.get(I.callee(g), heapwin.C.EMPTY)
        if heapwin.fn_cost(k, H, sigOf) <= heapwin.BUDGET:
            continue
        gen = dict(root='LeanVM.Guest.CoreMode.GenW', sub='HeapWG', final='heap_okW',
                   pre=f'{hcsig_ref(k)[:-len("sig")]}sig_pre' if in_sigs(k, R[k], shared) else 'sig_pre',
                   data=['LeanVM.Guest.CoreMode.Gen.«%s».DataC' % po[k][0]],
                   sigw='(fun f ↦ bif f == core.name then hcert.sig else (csigs.lookup f).getD {})')
        for name, text in heapwin.one(k, H, sigOf, [], epo, gen=gen):
            files[os.path.join(GENW, k, name + '.lean')] = text
        dirs.add(os.path.join(GENW, k))
    return files, dirs


def emit(R, check):
    import heap
    po = heap.pack_of()
    packs = collections.defaultdict(list)
    for k in sorted(R):
        packs[po[k][0]].append(k)
    files = {}
    shared, refs = sig_shared(R)
    for pack, ks in sorted(packs.items()):
        out = [HEADER.format(pack=pack, first=ks[0], more=len(ks) - 1)]
        used = set()
        for k in ks:
            out.append(f'\nnamespace LeanVM.Guest.Fn.«{k}»\n@[expose] public section\n{ldata(k, R[k], shared, used, refs)}'
                       f'\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        imps = sorted({po[c][0] for c in used})
        out[0] = out[0].replace('public import LeanVM.Guest.CoreMode.Defs\n', 'public import LeanVM.Guest.CoreMode.Defs\n' +
                                ''.join(f'public import LeanVM.Guest.CoreMode.Gen.«{q}».Sig\n' for q in imps))
        files[os.path.join(GEN, pack, 'DataC.lean')] = ''.join(out)
    sigp = collections.defaultdict(lambda: ([], []))
    for k in R:
        if in_sigs(k, R[k], shared):
            sigp[po[k][0]][0].append(k)
    for (c, t), n in refs.items():
        if n.endswith('.csig'):
            sigp[po[c][0]][1].append((c, t))
    for pack, (ks, cps) in sorted(sigp.items()):
        files[os.path.join(GEN, pack, 'Sig.lean')] = sig_file(pack, ks, R, cps)
    import glob
    stale = []
    for path in sorted(set(glob.glob(os.path.join(GEN, '*', 'Sig.lean')) + glob.glob(os.path.join(GEN, 'HcSig.lean')))
                       - set(files)):
        stale.append(path)
        if not check:
            os.remove(path)
    wfiles, wdirs = windows(R, po, shared)
    files.update(wfiles)
    for path in sorted(set(glob.glob(os.path.join(GENW, '*', '*.lean'))) - set(wfiles)):
        stale.append(path)
        if not check:
            os.remove(path)
    for d in sorted(set(glob.glob(os.path.join(GENW, '*'))) - wdirs):
        if not check:
            os.rmdir(d)
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
