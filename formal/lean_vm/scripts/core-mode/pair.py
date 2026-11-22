"""The order-aware pairing of the core route (`formal/notes/core-mode.md`): inference and checks.

The pass mirrors `CoreMode.pairOk` (`LeanVM/Guest/CoreMode/PairDefs.lean`), `Bridge.alignOk`'s pass with the heap events
consumed in order: the normalization stops at every `load` atom besides the flow hints; a `DEREF` of mode `cell`
consumes the head `load` at its cells (pointer cell, offset, word cell), skipping reads before it (a read's cell is
written, so a read the compiler shares with an earlier `load`'s `DEREF` needs none of its own), and records its offset
as a read (the oracle `O`) or a store (`S`) by the heap certificate (`heapOk`'s reads, from `heap.py`); flow hints and
jumps skip the reads at the head first. Every other instruction leaves the position. The certificate is the pair
`(O, S)` the pass finds; the kernel's check recomputes the pass and compares.

usage (from formal/lean_vm): python3 -I scripts/core-mode/pair.py [--fn NAME] [--emit] [--check]
"""
import os, sys, glob, re, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.join(HERE, '..'))
import genfiles  # noqa: E402
from compiled import BD as data  # noqa: E402
import align as AL  # noqa: E402
import heap

import windows  # noqa: E402
WIN = windows.ALIGN_WIN
# a function's own pairing window size (`windows.py`)
WINS = windows.own('PAIR_WIN')


def view(body):
    """The shared parse (`data.core_body`) as the pairing reads it: `align.view`'s, a `load` with its operands."""
    out = []
    for s in body:
        if s[0] == 'a':
            a = s[1]
            out.append(('hint', a[1]) if a[0] == 'hint' else ('load',) + a[1:] if a[0] == 'load' else ('atom', a[0]))
        elif s[0] == 'ite':
            out.append(('ite', s[1], view(s[2]), view(s[3])))
        elif s[0] == 'match':
            out.append(('match', s[1], [view(x) for x in s[2]]))
        else:
            out.append(s)
    return out


def body_of(text):
    return view(data.core_body(text))


def norm(z, stop):
    up, k, blk, idx = z
    while True:
        if idx < len(blk):
            s = blk[idx]
            if s[0] == 'atom' or (s[0] == 'hint' and not AL.flow_atom(s)) or (s[0] == 'load' and not stop(s)):
                k, idx = k + 1, idx + 1
                continue
            return (up, k, blk, idx)
        if not up:
            return (up, k, blk, idx)
        (kk, _, blk, idx), up = up[0], up[1:]
        k = kk + 1


class Fail(Exception):
    pass


def pair(F, body, A, locs, extra, pows, jt, ents, reads, cuts=()):
    """The pass: the reads' and stores' `DEREF` offsets and the pass's state at each offset of `cuts`, or `Fail`."""
    entry, code, stat = F['entry'], F['code'], F['stat']
    main = F['name'] == 'main'
    ex = dict(extra)
    loc = lambda v: ex[v] if v in ex else (locs[v] if v < len(locs) else 0)
    is_read = lambda s: s[0] == 'load' and (s[1], s[2], s[3]) in reads
    stopL = lambda s: True
    stopS = lambda s: not is_read(s)
    nL = lambda z: norm(z, stopL)
    nS = lambda z: norm(z, stopS)
    st = lambda o: stat.get(o)
    zero = lambda o: st(o) == ('k', 0, 0)
    nz = lambda o: st(o) is not None and st(o)[0] == 'k' and (st(o)[1], st(o)[2]) != (0, 0)
    self_ = lambda o: st(o) == ('fpg', 0, 0) or (main and st(o) == ('k', 1, 0))
    pc_at = lambda o: pows.get(st(o)[1]) if st(o) is not None and st(o)[0] == 'k' and st(o)[2] == 0 else None
    next_ = lambda o: st(o) is not None and st(o)[0] == 'fpg' and st(o)[1] != 0
    by_ent = {e: n for n, e in sorted(ents.items())}

    def fwd(i, t):
        if t is None or not entry + i < t:
            raise Fail(f'backward target at {i}')
        return t - entry

    def site(q, args, rets):
        s = F['sites'].get(q)
        return s if s is not None and s[0] == args and s[1] == rets else None

    def compiles(c, h):
        n = data.need(c, h)
        if n is None or any(loc(v) != cell for v, cell in n):
            raise Fail(f'hint {h[0]} does not compile {c[0]}')

    def fwd_j(i, oc, od, of):
        t = pc_at(od)
        return nz(oc) and self_(of) and t is not None and entry + i < t < entry + len(code)

    def jump(i, oc, od, of, z, tabs):
        if zero(oc):
            return z, []
        t = pc_at(od)
        if fwd_j(i, oc, od, of):
            return None, [(t - entry, z)]
        z = nS(z)
        s = AL.zhead(z)
        if s is None:
            raise Fail(f'jump at {i} past the body')
        if s[0] == 'ite':
            if loc(s[1]) != oc or not self_(of):
                raise Fail(f'ite at {i}')
            return nL(AL.enter(z, 0)), [(fwd(i, t), nL(AL.enter(z, 1)))]
        if s[0] in ('match', 'call', 'dispatch', 'ret') and not nz(oc):
            raise Fail(f'{s[0]} at {i} on a cell not a nonzero constant')
        if s[0] == 'match':
            a = F['arms'].get(od)
            if not self_(of) or a is None or a[0] != s[1]:
                raise Fail(f'match at {i}')
            if any(t[0] == a[1] and AL.key(t[1]) == AL.key(z) and i < t[2] for t in tabs):
                return None, []
            return None, [(fwd(i, jt.get(a[1] + j)), nL(AL.enter(z, j))) for j in range(len(s[2]))]
        if s[0] == 'call':
            si = site(of, s[2], s[3])
            if si is None or t is None or by_ent.get(t) != s[1]:
                raise Fail(f'call at {i}')
            return None, [(fwd(i, si[3]), nL(AL.nxt(z)))]
        if s[0] == 'callIf':
            if loc(s[1]) != oc or t is None or by_ent.get(t) != s[2]:
                raise Fail(f'callIf at {i}')
            ca = nL(AL.nxt(z))
            if next_(of):
                two, more = AL.pos2(ca)
                if two != [('ret', [])] or more:
                    raise Fail(f'tail at {i}')
                return ca, []
            si = site(of, s[3], [])
            if si is None or si[3] != entry + i + 1:
                raise Fail(f'callIf site at {i}')
            return ca, []
        if s[0] == 'dispatch':
            si = site(of, s[3], s[4])
            if si is None or si[4] != od or od == 0:
                raise Fail(f'dispatch at {i}')
            return None, [(fwd(i, si[3]), nL(AL.nxt(z)))]
        if s[0] == 'ret':
            if (main and self_(of) and t == AL.HALT) or (not main and od == 0 and of == 1):
                return None, []
            raise Fail(f'ret at {i}')
        raise Fail(f'jump at {i} on {s[0]}')

    def deref(o1, o2, o3, z):
        """The head `load` at the cells, reads before it skipped: the position past it and whether it reads."""
        zz = z
        while True:
            s = AL.zhead(zz)
            if s is None or s[0] != 'load':
                return z, None
            if (loc(s[2]), s[3], loc(s[1])) == (o1, o2, o3):
                return nL(AL.nxt(zz)), is_read(s)
            if not is_read(s):
                return z, None
            zz = nL(AL.nxt(zz))

    pcs = [pc for pc, _ in A['hints']]
    if A['entry'] != entry or any(x >= y for x, y in zip(pcs, pcs[1:])) or any(x < entry for x in pcs):
        raise Fail('advice not by increasing pc from the entry')
    hints = dict(A['hints'])
    flow = AL.data_flow()
    cut_set, states = set(cuts), {}
    O, S = [], []
    cur, pend, nd, tabs = ((), 0, body, 0), [], 0, []
    for i, (op, a) in enumerate(code):
        if i in cut_set:
            states[i] = (i, nd, None if cur is None else AL.key(cur), [(o, AL.key(z)) for o, z in pend],
                         [(b, AL.key(z), m) for b, z, m in tabs])
        if entry + i in hints:
            nd += 1
        n = 0
        while n < len(pend) and pend[n][0] == i:
            n += 1
        here, pend = pend[:n], pend[n:]
        c = cur if cur is not None else (here[0][1] if here else None)
        if c is None:
            continue
        if any(AL.key(p[1]) != AL.key(c) for p in here):
            raise Fail(f'join at {i}')
        z = nL(c)
        for h in hints.get(entry + i, []):
            if h[0] not in flow:
                continue
            z = nS(z)
            s = AL.zhead(z)
            if s is None or s[0] != 'hint':
                raise Fail(f'hint {h[0]} at {i} without its atom')
            compiles(s[1], h)
            z = nL(AL.nxt(z))
        if op == '.jump':
            cur, tg = jump(i, a[0], a[1], a[2], z, tabs)
            zs = nS(z)
            s = AL.zhead(zs)
            if tg and s is not None and s[0] == 'match' and not fwd_j(i, a[0], a[1], a[2]) and \
                    F['arms'].get(a[1]) is not None:
                tabs.insert(0, (F['arms'][a[1]][1], zs, min(min(o for o, _ in tg), 1 << 64)))
        elif op == '.deref' and len(a) == 4 and a[3] == ('id', '.cell'):
            cur, r = deref(a[0], a[1], a[2], z)
            tg = []
            if r is True:
                O.append(i)
            elif r is False:
                S.append(i)
            elif F['arms'].get(a[2]) is not None and F['arms'][a[2]][1] == a[1] and loc(F['arms'][a[2]][0]) == a[0]:
                O.append(i)  # a read of the jump table (`CoreMode.jtd`), consuming nothing
            elif F['arms'].get(a[2]) is None and a[2] != 0 and any(s[4] == a[2] for s in F['sites'].values()):
                O.append(i)  # a dispatch's read of the jump table (`CoreMode.jtd`, checked at its `JUMP`: `jtdGo`)
        else:
            cur, tg = z, []
        for t in reversed(tg):
            n = 0
            while n < len(pend) and pend[n][0] < t[0]:
                n += 1
            pend.insert(n, t)
    if cur is not None or pend:
        raise Fail('falls off the end')
    if len(code) in cut_set:
        states[len(code)] = (len(code), nd, None, [], [(b, AL.key(z), m) for b, z, m in tabs])
    return O, S, states


def count_loads(body):
    n = 0
    for s in body:
        if s[0] == 'load':
            n += 1
        elif s[0] == 'ite':
            n += count_loads(s[2]) + count_loads(s[3])
        elif s[0] == 'match':
            n += sum(count_loads(x) for x in s[2])
    return n


def collect():
    """Each function passing `heapOk`, with what its pairing reads and the pass's result; computed once while its
    inputs are unchanged (`memo.py`)."""
    if '--fn' in sys.argv:
        return _collect()
    import memo
    return memo.cached('pair.collect', _collect)


def _collect():
    res = {k: heap.Fn(k).run() for k in heap.scope_fns()}
    ok = sorted(k for k, f in res.items() if f.fail is None)
    reads = {k: set(res[k].wit) for k in ok}
    # bodies with calls, by the check with calls (`callc.py`)
    import callc
    CR, _ = callc.results()
    for k, r in CR.items():
        reads[k] = set(r['cert'].reads)
    # loop helpers, by the check's loop rules at their callees' signatures (`loopcc.py`)
    import loopcc
    LCR, _ = loopcc.results()
    for k, r in LCR.items():
        reads[k] = set(r['cert'].reads)
    ok = sorted(set(ok) | set(CR) | set(LCR))
    only = sys.argv[sys.argv.index('--fn') + 1] if '--fn' in sys.argv else None
    if only:
        ok = [only]
    texts = data.core_texts()
    bundles = data.bundles()
    advice = data.advice()
    fns = AL.functions()
    pows = AL.pow_table()
    jt = AL.jump_table(pows)
    entry_by_name = {F['name']: F['entry'] for F in fns.values()}
    out, fails = {}, {}
    for k in ok:
        if k not in fns or k not in texts:
            fails[k] = 'no compiled code'
            continue
        F, B = fns[k], bundles[k]
        A = advice[F['entry']]
        body = body_of(texts[k])
        callees = sorted({s[1] if s[0] == 'call' else s[2] for s in AL.walk_stmts(body) if s[0] in ('call', 'callIf')})
        ents = {n: entry_by_name[n] for n in callees if n in entry_by_name}
        n = len(F['code'])
        win = WINS.get(k, WIN)
        cuts = list(range(0, n, win)) + [n] if n > win else []
        try:
            extra, _ = AL.align(F, AL.body_of(texts[k]), A, B['locs'], B['plumb'], pows, jt, ents)
            O, S, states = pair(F, body, A, B['locs'], extra, pows, jt, ents, reads[k], cuts)
        except (Fail, AL.Fail) as e:
            fails[k] = str(e)
            continue
        out[k] = dict(key=k, entry=F['entry'], O=O, S=S, states=[states[c] for c in cuts], n=n, j=A['j'], jt0=jt0_of(F),
                      bpack=B['pack'], loads=count_loads(body), reads=len(reads[k]), locs=B['locs'], extra=dict(extra),
                      kind='c' if k in CR else ('lc' if k in LCR else 'm1'))
    return out, fails


GUEST = data.ROOT
GEN = os.path.join(GUEST, 'CoreMode', 'Gen')
HEADER = genfiles.header('core-mode/pair.py --emit')


def nums(l):
    return '[' + ', '.join(map(str, l)) + ']'


def offs_defs(k, f):
    return (f'/-- `{k}`: the offsets of its reads\' `DEREF`s, the oracle. -/\n'
            f'noncomputable def pairO : Exec.Trie Unit :=\n  CoreMode.offsT {nums(f["O"])}\n\n'
            f'/-- `{k}`: the offsets of its stores\' `DEREF`s. -/\n'
            f'noncomputable def pairS : Exec.Trie Unit :=\n  CoreMode.offsT {nums(f["S"])}\n')


def args(k, f, ctx='alignCtx'):
    return f'{ctx} hcert pairO pairS Fn.«{k}».core.body Fn.«{k}».code.code Fn.«{k}».advice'


def argsS(k, ctx):
    return f'{ctx} hcert pairO pairS Fn.«{k}».core.body Fn.«{k}».code.chunks Fn.«{k}».advice'


def packed_ctx(k):
    """Whether `k`'s alignment context has its cells packed ahead (`alignCtxP`, `Bridge/AlignCtx/<k>/`): its pairing
    windows then read that one, the check taken through `alignCtxEq`."""
    return 'alignCtxP' in open(os.path.join(GUEST, 'Bridge', 'AlignCtx', k, 'Ctx.lean'), encoding='utf-8').read()


ns, imports = AL.ns, AL.imports


def data_mod(pack, f):
    """The module of the function's heap certificate: the check without calls', or the check with calls'."""
    return f'LeanVM.Guest.CoreMode.Gen.«{pack}».' + {'c': 'DataC', 'lc': 'DataLC'}.get(f.get('kind'), 'Data')


def render_pack(pack, fs):
    mod = f'LeanVM.Guest.CoreMode.Gen.«{pack}».Pair'
    defs = ''.join(f'noncomputable def Fn.«{f["key"]}».pairO : Exec.Trie Unit := CoreMode.offsT {nums(f["O"])}\n'
                   f'noncomputable def Fn.«{f["key"]}».pairS : Exec.Trie Unit := CoreMode.offsT {nums(f["S"])}\n' for f in fs)
    thms = ''.join(f'theorem Fn.«{f["key"]}».pair_ok : CoreMode.pairOk alignCtx hcert pairO pairS core.body code.code '
                   f'advice = true := by decide +kernel\n' for f in fs)
    return {os.path.join(GEN, pack, 'Pair.lean'): ''.join([
        HEADER(mod=mod, what=f"The kernel's pairing checks of `{fs[0]['key']}` and {len(fs) - 1} more: each "
                      "function's `pairO`, the offsets of its reads' `DEREF`s (the oracle), and `pairS`, of its stores', "
                      "its `load`s paired with its `DEREF`s in order."),
        imports(['LeanVM.Guest.CoreMode.PairDefs', f'LeanVM.Guest.CoreMode.GlueA.«{pack}»'] + [data_mod(pack, f) for f in fs]
                + [f'LeanVM.Guest.Bridge.Align.«{f["bpack"]}»' for f in fs]),
        'set_option Elab.async false\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\n'
        '@[expose] public section\n\n', defs,
        '\nend\n\npublic section\n\n', thms, '\nend\n\nend LeanVM.Guest\n'])}


def jt0_of(F):
    """The function's first jump-table slot (the glue's `Fn.«k».jt0`, `glue.py`), or None without table jumps."""
    return min((b for _, b in F['arms'].values()), default=None)


def kst(k, f, K):
    """`AL.kst`, a registered table jump's slot from the function's first (`Fn.«k».jt0`): the states stay put when the
    jump table moves."""
    i, nd, cur, pend, tabs = K
    c = 'none' if cur is None else f'some ({AL.cur_lit(cur)})'
    pe = ', '.join(f'({o}, ({AL.cur_lit(z)}))' for o, z in pend)
    ta = ', '.join(f'(Fn.«{k}».jt0 + {b - f["jt0"]}, ({AL.cur_lit(z)}), {m})' for b, z, m in tabs)
    return f'⟨{i}, {nd}, {c}, [{pe}], [{ta}]⟩'


def cut_of(clens, i):
    """Offset `i` of the code as a cut `(p, r)` of its chunks (`Bridge.PCut`): chunk `p`, offset `r` in it; the code's end
    is `(len, 0)`."""
    p = 0
    while p < len(clens) and i >= clens[p]:
        i -= clens[p]; p += 1
    assert p < len(clens) or i == 0
    return f'({p}, {i})'


def render_win(pack, f):
    k = f['key']
    # the windows over slices of the code's chunks (`CoreMode/PairSlice.lean`): none walks the code before it
    clens = AL.functions()[k]['clens']
    assert sum(clens) == f['states'][-1][0]
    base = f'LeanVM.Guest.CoreMode.Gen.«{pack}».«{k}»'
    ks = f['states']
    files = {}
    packed = packed_ctx(k)
    wctx = 'alignCtxP' if packed else 'alignCtx'
    defs = ''.join(f"/-- `{k}`: the pairing's state at offset {K[0]}. -/\ndef pairK{n} : Bridge.KSt :=\n  {kst(k, f, K)}\n\n"
                   for n, K in enumerate(ks))
    files[os.path.join(GEN, pack, k, 'Ctx.lean')] = (
        HEADER(mod=f'{base}.Ctx', what=f"`{k}`'s pairing oracle and the pass's states at its windows' ends.")
        + imports(['LeanVM.Guest.CoreMode.PairSlice', f'LeanVM.Guest.CoreMode.GlueA.«{pack}»', data_mod(pack, f),
                   f'LeanVM.Guest.Bridge.AlignCtx.«{k}».Ctx'])
        + ns(k, f'''@[expose] public section

{offs_defs(k, f)}
{defs}end
'''))
    for n in range(len(ks) - 1):
        files[os.path.join(GEN, pack, k, f'W{n}.lean')] = (
            HEADER(mod=f'{base}.W{n}', what=f"`{k}`'s pairing pass from offset {ks[n][0]} to {ks[n + 1][0]}.")
            + imports([f'{base}.Ctx']) + 'set_option Elab.async false\n\n' + ns(k, f'''public section

/-- `{k}`: the pairing from offset {ks[n][0]} to {ks[n + 1][0]}. -/
theorem pairWin{n} : CoreMode.winOkHS {argsS(k, wctx)} {cut_of(clens, ks[n][0])} {cut_of(clens, ks[n + 1][0])} pairK{n}
    pairK{n + 1} = true := by
  decide +kernel

end
'''))
    chain = 'pairEndOk'
    for n in reversed(range(len(ks) - 1)):
        chain = f'(And.intro pairWin{n} {chain})'
    files[os.path.join(GEN, pack, k, 'Ok.lean')] = (
        HEADER(mod=f'{base}.Ok', what=f"`{k}`'s pairing check, by its windows.")
        + imports(['LeanVM.Guest.CoreMode.PairSlice', f'LeanVM.Guest.Bridge.AlignCtx.«{k}».Ok']
                  + [f'{base}.W{n}' for n in range(len(ks) - 1)])
        + ns(k, f'''public section

/-- `{k}`: the pairing's last state is at the end. -/
theorem pairEndOk : CoreMode.chainEndS Fn.«{k}».code.chunks ({len(clens)}, 0) pairK{len(ks) - 1} = true := by
  decide +kernel

/-- `{k}`: its `load`s pair with its `DEREF`s in order, the oracle naming its reads{" (its context " + wctx + ")" if packed else ""}. -/
theorem pair_ok{"P" if packed else ""} : CoreMode.pairOk {args(k, f, wctx)} = true :=
  CoreMode.pairOk_of_chainS alignPreOk (ks := [{', '.join(f'({cut_of(clens, ks[n][0])}, pairK{n})' for n in range(1, len(ks)))}])
    {chain}
{f'''
/-- `{k}`: its `load`s pair with its `DEREF`s in order, the oracle naming its reads. -/
theorem pair_ok : CoreMode.pairOk {args(k, f)} = true :=
  alignCtxEq ▸ pair_okP
''' if packed else ''}
end
'''))
    # the alignment pass (the hint bridge's `Bridge.alignOk`), in windows from the same states normalized as it holds
    # them (`CoreMode.alignKOf`), the first the pass's start
    al = lambda n: 'pairK0' if n == 0 else f'(CoreMode.alignKOf {wctx} Fn.«{k}».core.body pairK{n})'
    aargs = f'{wctx} Fn.«{k}».core.body Fn.«{k}».code.code Fn.«{k}».advice'
    for n in range(len(ks) - 1):
        files[os.path.join(GEN, pack, k, f'AW{n}.lean')] = (
            HEADER(mod=f'{base}.AW{n}', what=f"`{k}`'s alignment pass from offset {ks[n][0]} to {ks[n + 1][0]}.")
            + imports([f'{base}.Ctx', 'LeanVM.Guest.CoreMode.AlignK']) + 'set_option Elab.async false\n\n' + ns(k, f'''public section

/-- `{k}`: the alignment pass from offset {ks[n][0]} to {ks[n + 1][0]}. -/
theorem alignWin{n} : Bridge.winOk {aargs} {al(n)} {al(n + 1)} = true := by
  decide +kernel

end
'''))
    achain = 'alignEndOk'
    for n in reversed(range(len(ks) - 1)):
        achain = f'(And.intro alignWin{n} {achain})'
    files[os.path.join(GUEST, 'CoreMode', 'AlignOk', f'{k}.lean')] = (
        HEADER(mod=f'LeanVM.Guest.CoreMode.AlignOk.«{k}»', what=f"`{k}` aligns with its body (the hint bridge's "
                      "check), by windows from its pairing's states.")
        + imports(['LeanVM.Guest.Bridge.AlignRun', 'LeanVM.Guest.CoreMode.AlignK', f'LeanVM.Guest.Bridge.AlignCtx.«{k}».Ok']
                  + [f'{base}.AW{n}' for n in range(len(ks) - 1)])
        + ns(k, f'''public section

/-- `{k}`: the alignment pass's last state is at the end. -/
theorem alignEndOk : Bridge.chainEnd Fn.«{k}».code.code {al(len(ks) - 1)} = true := by
  decide +kernel

/-- `{k}` aligns with its body{" (its context " + wctx + ")" if packed else ""}. -/
theorem alignOk{"P" if packed else ""} : Bridge.alignOk {aargs} = true :=
  Bridge.alignOk_of_chain alignPreOk (ks := [{', '.join(al(n) for n in range(1, len(ks)))}])
    {achain}
{f'''
/-- `{k}` aligns with its body. -/
theorem alignOk : Bridge.alignOk alignCtx Fn.«{k}».core.body Fn.«{k}».code.code Fn.«{k}».advice = true :=
  alignCtxEq ▸ alignOkP
''' if packed else ''}
end
'''))
    return files


def emit(out, check):
    po = heap.pack_of()
    packs = collections.defaultdict(list)
    files = {}
    for k in sorted(out):
        f = out[k]
        if f['states']:
            files.update(render_win(po[k][0], f))
        else:
            packs[po[k][0]].append(f)
    for pack, fs in sorted(packs.items()):
        files.update(render_pack(pack, fs))
    existing = set(glob.glob(os.path.join(GEN, '*', 'Pair.lean'))) | set(glob.glob(os.path.join(GEN, '*', '*', '*.lean'))) | \
        set(glob.glob(os.path.join(GUEST, 'CoreMode', 'AlignOk', '*.lean')))
    stale = genfiles.sync(files, existing, check)
    lines = sum(t.count('\n') for t in files.values())
    print(f'pair: {len(files)} modules, {lines} lines' + (f'; {len(stale)} stale' if check else ''))
    genfiles.fail_if_stale(stale, check, data.LEAN_VM, 10)


def main():
    out, fails = collect()
    print(f'pairing: {len(out)} of {len(out) + len(fails)} functions pass; {sum(len(f["O"]) for f in out.values())} read '
          f'and {sum(len(f["S"]) for f in out.values())} store DEREFs; {sum(f["loads"] for f in out.values())} loads')
    by = collections.Counter(re.sub(r' \S+$', '', r.split(' at ')[0]) for r in fails.values())
    print('  failures by cause:', dict(by.most_common()))
    for k, r in sorted(fails.items())[:20]:
        print('   ', k, r)
    if '--emit' in sys.argv:
        emit(out, '--check' in sys.argv)
    return out


if __name__ == '__main__':
    main()
