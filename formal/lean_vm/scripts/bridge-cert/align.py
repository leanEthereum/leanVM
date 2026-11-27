"""The hint bridge's alignment contexts (`LeanVM/Guest/Bridge/Align/*.lean`; a long function's, `AlignCtx/*/*.lean`).

The pass mirrors `Bridge.alignOk` (`LeanVM/Guest/Bridge/AlignDefs.lean`) over the generated data: a forward
walk over each function's code pairing its flow hints, branches, table jumps, call sites and returns with
body positions (zippers into the body), finding the cells only hints touch as `gen.py` does. It writes, per
pack of the bundles, each function's context and the kernel's checks of its hint-only cells; the alignment
itself follows from the core route's pairing (`core-mode/pair.py`, `CoreMode.alignOk_of_pairOk`). A function
longer than `WIN` instructions has a context of its own (`AlignCtx/<fn>/`), its checks but the pass
(`alignPreOk`) apart; one longer than `SLICE` instructions has its cells packed ahead in pieces
(`Bridge.packSt`), so no module walks its whole cells.
`--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/align.py [--check]
"""
import os, sys, glob, re, functools
if os.path.dirname(os.path.abspath(__file__)) not in sys.path:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
from data import parse, as_list, head, defs

OUT = os.path.join(data.ROOT, 'Bridge', 'Align')
HALT = data.HALT


def view(body):
    """The shared parse (`data.core_body`) as the alignment reads it: an atom `('atom', kind)`, a hint
    `('hint', core_hint)`, the rest as parsed."""
    out = []
    for s in body:
        if s[0] == 'a':
            out.append(('hint', s[1][1]) if s[1][0] == 'hint' else ('atom', s[1][0]))
        elif s[0] == 'ite':
            out.append(('ite', s[1], view(s[2]), view(s[3])))
        elif s[0] == 'match':
            out.append(('match', s[1], [view(x) for x in s[2]]))
        else:
            out.append(s)
    return out


def body_of(text):
    return view(data.core_body(text))


@functools.cache
def functions():
    """Each compiled function's name, entry, code with operands and plumbing, by stable name."""
    out = {}
    for key, (_, blk) in data.bundle_blocks().items():
        name, entry, _, _ = data.code_of(blk)
        chunks = data.chunks_of(blk)
        code = [i for ch in chunks for i in ch]
        stat, sites, arms, chains, nxt = {}, [], [], [], set()
        pl = re.search(r'noncomputable def plumb : B2C\.Plumb where\n(.*?)\n(?:/--|\Z)', blk, re.S)
        if pl:
            pt = pl.group(1)
            st = re.search(r'^  stat := (.*)$', pt, re.M)
            if st:
                for m in re.finditer(r'\((\d+), \(\.(k|fpg) (\d+)(?: (\d+))?\)\)', st.group(1)):
                    stat[int(m.group(1))] = (m.group(2), int(m.group(3)), int(m.group(4) or 0))
            si = re.search(r'^  sites := (.*)$', pt, re.M)
            if si:
                for m in re.finditer(r'⟨\[([^\]]*)\], \[([^\]]*)\], (\d+), (\d+), (\d+)⟩', si.group(1)):
                    nums = lambda s: [int(x) for x in s.split(',') if x.strip()]
                    sites.append((nums(m.group(1)), nums(m.group(2)), int(m.group(3)), int(m.group(4)),
                                  int(m.group(5))))
            ar = re.search(r'^  arms := (.*)$', pt, re.M)
            if ar:
                arms = [tuple(int(x) for x in m.groups()) for m in re.finditer(r'\((\d+), (\d+), (\d+)\)', ar.group(1))]
            nx = re.search(r'^  nxt := \[([^\]]*)\]', pt, re.M)
            if nx:
                nxt = {int(x) for x in nx.group(1).split(',') if x.strip()}
            ch = re.search(r'^  chains := (.*)$', pt, re.M)
            if ch:
                for m in re.finditer(r'\((\d+), (\d+), \[([^\]]*)\], (\d+), (\d+)\)', ch.group(1)):
                    chains.append((int(m.group(1)), int(m.group(2)), [int(x) for x in m.group(3).split(',') if x.strip()],
                                   int(m.group(4)), int(m.group(5))))
        by_od = {}
        for x, od, base in arms:
            by_od[od] = (x, base)
        for _, _, ts, y, b in chains:
            for t in ts:
                by_od[t] = (y, b)
        by_q = {}
        for si in sites:
            by_q[si[2]] = si
        out[key] = dict(name=name, entry=entry, code=code, stat=stat, sites=by_q, arms=by_od, nxt=nxt,
                        clens=[len(ch) for ch in chunks])
    return out


def pow_table():
    t = open(data.ROOT + '/Data/Pows.lean', encoding='utf-8').read()
    return {int(k): int(e) for k, e in re.findall(r'\.node (\d+) (\d+)\b', t)}


def jump_table(pows):
    t = ''.join(open(p, encoding='utf-8').read() for p in sorted(glob.glob(data.LEAN_VM + '/../Statement/Data/Bytecode*.lean')))
    ds = defs(t)
    env = lambda n: parse(ds[n])
    jt = {}
    for c in sorted((n for n in ds if re.fullmatch(r'f0c\d+', n)), key=lambda n: int(n[3:])):
        for x in as_list(env(c), env):
            h, a = head(x)
            if h == '.set' and a[2] == 0 and a[1] in pows:
                jt[a[0]] = pows[a[1]]
    return jt


def flow_atom(s):
    return s[0] == 'hint' and s[1][0] not in ('alloc', 'allocDyn')


def sub_block(s, c):
    if s[0] == 'ite':
        return s[2] if c == 0 else s[3]
    if s[0] == 'match':
        return s[2][c] if c < len(s[2]) else []
    return []


# A zipper mirrors `Bridge.Zip`: `(up, k, blk, idx)`, the statements from `blk[idx]`, each enclosing level
# `(k', c, pblk, pidx)` with the statements after it from `pblk[pidx]`.

def key(z):
    return (tuple((e[0], e[1]) for e in z[0]), z[1])


def norm(z):
    up, k, blk, idx = z
    while True:
        if idx < len(blk):
            s = blk[idx]
            if s[0] == 'atom' or (s[0] == 'hint' and not flow_atom(s)):
                k, idx = k + 1, idx + 1
                continue
            return (up, k, blk, idx)
        if not up:
            return (up, k, blk, idx)
        (kk, _, blk, idx), up = up[0], up[1:]
        k = kk + 1


def zhead(z):
    return z[2][z[3]] if z[3] < len(z[2]) else None


def enter(z, c):
    up, k, blk, idx = z
    return (((k, c, blk, idx + 1),) + up, 0, sub_block(blk[idx], c), 0)


def nxt(z):
    up, k, blk, idx = z
    return (up, k + 1, blk, idx + 1)


def pos2(z):
    """The first two statements left."""
    out = list(z[2][z[3]:z[3] + 2])
    for e in z[0]:
        if len(out) >= 2:
            break
        out += e[2][e[3]:e[3] + 2]
    return out[:2], len(out) > 2 or any(len(e[2]) > e[3] + 2 for e in z[0]) or len(z[2]) > z[3] + 2


class Fail(Exception):
    pass


def align(F, body, A, locs, plumb_cells, pows, jt, ents, cuts=()):
    """The alignment pass: the hint-only cells and the pass's state at each offset of `cuts`
    (`(i, hints consumed, cursor falling in, arrivals pending)`), or `Fail`."""
    entry, code, stat = F['entry'], F['code'], F['stat']
    main = F['name'] == 'main'
    extra = {}
    loc = lambda v: extra[v] if v in extra else (locs[v] if v < len(locs) else 0)
    st = lambda o: stat.get(o)
    zero = lambda o: st(o) == ('k', 0, 0)
    nz = lambda o: st(o) is not None and st(o)[0] == 'k' and (st(o)[1], st(o)[2]) != (0, 0)
    self_ = lambda o: st(o) == ('fpg', 0, 0) or (main and st(o) == ('k', 1, 0))
    pc_at = lambda o: pows.get(st(o)[1]) if st(o) is not None and st(o)[0] == 'k' and st(o)[2] == 0 else None
    # `AlignCtx.nextAt`: a next-frame product among the fixed cells, or a cell past the frame (`Plumb.nxt`)
    next_ = lambda o: (st(o)[0] == 'fpg' and st(o)[1] != 0) if st(o) is not None else o in F['nxt']

    def fwd(i, t):
        if t is None or not entry + i < t:
            raise Fail(f'backward target at {i}')
        return t - entry

    by_ent = {}
    for n, e in sorted(ents.items()):
        by_ent[e] = n

    def site(q, args, rets):
        s = F['sites'].get(q)
        return s if s is not None and s[0] == args and s[1] == rets else None

    def compiles(c, h):
        n = data.need(c, h)
        if n is None:
            raise Fail(f'hint {h[0]} does not compile {c[0]}')
        for v, cell in n:
            if loc(v) == cell:
                continue
            base = locs[v] if v < len(locs) else 0
            if base < 2 and v not in extra and cell >= 2 and cell not in locs and cell not in plumb_cells:
                extra[v] = cell
            else:
                raise Fail(f'hint {h[0]} cells')

    def fwd_j(i, oc, od, of):
        t = pc_at(od)
        return nz(oc) and self_(of) and t is not None and entry + i < t < entry + len(code)

    def jump(i, oc, od, of, z, tabs):
        if zero(oc):
            return z, []
        t = pc_at(od)
        if fwd_j(i, oc, od, of):
            return None, [(t - entry, z)]
        s = zhead(z)
        if s is None:
            raise Fail(f'jump at {i} past the body')
        if s[0] == 'ite':
            if loc(s[1]) != oc or not self_(of):
                raise Fail(f'ite at {i}')
            return norm(enter(z, 0)), [(fwd(i, t), norm(enter(z, 1)))]
        if s[0] in ('match', 'call', 'dispatch', 'ret') and not nz(oc):
            raise Fail(f'{s[0]} at {i} on a cell not a nonzero constant')
        if s[0] == 'match':
            a = F['arms'].get(od)
            if not self_(of) or a is None or a[0] != s[1]:
                raise Fail(f'match at {i}')
            if any(t[0] == a[1] and key(t[1]) == key(z) and i < t[2] for t in tabs):
                return None, []
            return None, [(fwd(i, jt.get(a[1] + j)), norm(enter(z, j))) for j in range(len(s[2]))]
        if s[0] == 'call':
            si = site(of, s[2], s[3])
            if si is None or t is None or by_ent.get(t) != s[1]:
                raise Fail(f'call at {i}')
            return None, [(fwd(i, si[3]), norm(nxt(z)))]
        if s[0] == 'callIf':
            if loc(s[1]) != oc or t is None or by_ent.get(t) != s[2]:
                raise Fail(f'callIf at {i}')
            ca = norm(nxt(z))
            if next_(of):
                two, more = pos2(ca)
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
            return None, [(fwd(i, si[3]), norm(nxt(z)))]
        if s[0] == 'ret':
            if (main and self_(of) and t == HALT) or (not main and od == 0 and of == 1):
                return None, []
            raise Fail(f'ret at {i}')
        raise Fail(f'jump at {i} on {s[0]}')

    if any(c >= 1 << 20 for c in locs):
        raise Fail('a cell past 2^20')
    pcs = [pc for pc, _ in A['hints']]
    if A['entry'] != entry or any(x >= y for x, y in zip(pcs, pcs[1:])) or any(x < entry for x in pcs):
        raise Fail('advice not by increasing pc from the entry')
    hints = dict(A['hints'])
    flow = data_flow()
    cut_set, states = set(cuts), {}
    cur, pend, nd, tabs = ((), 0, body, 0), [], 0, []
    for i, (op, a) in enumerate(code):
        if i in cut_set:
            states[i] = (i, nd, None if cur is None else key(cur), [(o, key(z)) for o, z in pend],
                         [(b, key(z), m) for b, z, m in tabs])
        if entry + i in hints:
            nd += 1
        n = 0
        while n < len(pend) and pend[n][0] == i:
            n += 1
        here, pend = pend[:n], pend[n:]
        c = cur if cur is not None else (here[0][1] if here else None)
        if c is None:
            continue
        if any(key(p[1]) != key(c) for p in here):
            raise Fail(f'join at {i}')
        z = norm(c)
        for h in hints.get(entry + i, []):
            if h[0] not in flow:
                continue
            s = zhead(z)
            if s is None or s[0] != 'hint':
                raise Fail(f'hint {h[0]} at {i} without its atom')
            compiles(s[1], h)
            z = norm(nxt(z))
        if op == '.jump':
            cur, tg = jump(i, a[0], a[1], a[2], z, tabs)
            s = zhead(z)
            if tg and s is not None and s[0] == 'match' and not fwd_j(i, a[0], a[1], a[2]) and \
                    F['arms'].get(a[1]) is not None:
                tabs.insert(0, (F['arms'][a[1]][1], z, min(min(o for o, _ in tg), 1 << 64)))
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
        states[len(code)] = (len(code), nd, None, [], [(b, key(z), m) for b, z, m in tabs])
    return sorted(extra.items()), states


def data_flow():
    return data.FLOW


import windows  # noqa: E402
WIN = windows.ALIGN_WIN
SLICE = 1 << 16
PIECE = 20000
# a long function's alignment context (its pass is checked in windows from the core route's pairing states,
# `scripts/core-mode/pair.py`, `CoreMode/AlignOk/<fn>.lean`)
OUTW = os.path.join(data.ROOT, 'Bridge', 'AlignCtx')
# where the windows and their states were before
OLDW = os.path.join(data.ROOT, 'Bridge', 'AlignWin')
HEAD = genfiles.header('bridge-cert/align.py')


def ctx_def(f):
    k = f['key']
    cells = '[' + ', '.join(f'({v}, {c})' for v, c in f['extra']) + ']'
    ents = ents_lit(f)
    return cells, f'''/-- `{k}`: what its alignment check reads beyond its body and code. -/
noncomputable def alignCtx : Bridge.AlignCtx :=
  Bridge.AlignCtx.ofData Fn.«{k}».cert.locs {cells} Fn.«{k}».code.entryPc {"true" if f["main"] else "false"}
    Fn.«{k}».plumb Data.powTree Data.jtTrie {ents} CoreMode.haltPc Fn.«{k}».code.instructionCount
'''


def cells_thm(f, cells):
    k = f['key']
    return f'''/-- `{k}`: its hint-only cells are fresh. -/
theorem alignCellsOk :
    Bridge.cellsFresh Fn.«{k}».cert.locs (Bridge.plumbCells Fn.«{k}».plumb) {cells} = true := by
  decide +kernel
'''


def ents_lit(f):
    """The callees with their entries, each entry by its stable name (`CoreMode/GlueE/<pack>.lean`'s `Fn.«k».entry`, the
    glue), not as a number."""
    return '[' + ', '.join(f'("{n}", Fn.«{c}».entry)' for n, c, _ in f['entk']) + ']'


def bases(f, pack):
    return ['LeanVM.Guest.Bridge.AlignDefs', 'Statement.Data.AdviceHints', 'LeanVM.Guest.Data.Pows', 'LeanVM.Guest.CoreMode.GlueG',
            f'LeanVM.Guest.Pack.«{pack}».Bundle',
            f'LeanVM.Guest.Pack.«{f["core_pack"]}».Core' if f['core_pack'] else data.core_module(f['key'])] + \
        [f'LeanVM.Guest.CoreMode.GlueE.«{q}»' for _, _, q in f['entk']]


HOME = {}


def glue_a(k):
    """The glue module naming function `k`'s advice and index (`CoreMode/GlueA/<pack>.lean`, by the pack holding its
    core, as `scripts/core-mode/glue.py` writes it)."""
    if not HOME:
        HOME.update((k, bs[0][0]) for k, bs in data.core_blocks().items())
    return f'LeanVM.Guest.CoreMode.GlueA.«{HOME[k]}»'


def imports(ms):
    # the checks read the advice's values, which `Statement/Data` does not expose
    return ''.join(f'public import {m}\n' for m in sorted(set(ms))) + 'import all Statement.Data.AdviceHints\n\n'


def ns(k, body):
    return f'namespace LeanVM.Guest.Fn.«{k}»\n\nopen LeanVM.Guest\n\n{body}\nend LeanVM.Guest.Fn.«{k}»\n'


def ctx_line(f):
    """`alignCtx` as one declaration of the pack's section (`progal.CTX1` reads it back)."""
    k = f['key']
    cells = '[' + ', '.join(f'({v}, {c})' for v, c in f['extra']) + ']'
    ents = ents_lit(f)
    return cells, (f'noncomputable def Fn.«{k}».alignCtx : Bridge.AlignCtx := Bridge.AlignCtx.ofData cert.locs {cells} '
                   f'code.entryPc {"true" if f["main"] else "false"} plumb Data.powTree Data.jtTrie {ents} CoreMode.haltPc '
                   f'code.instructionCount\n')


def render(pack, fns):
    ctxs = [ctx_line(f) for f in fns]
    thms = []
    for f, (cells, _) in zip(fns, ctxs):
        k = f['key']
        if cells == '[]':
            thms.append(f'align_chk% «{k}»\n'); continue
        thms.append((k, 'alignCellsOk', f'Bridge.cellsFresh cert.locs (Bridge.plumbCells plumb) {cells} = true',
                     'decide +kernel'))
    return (HEAD(mod=f'LeanVM.Guest.Bridge.Align.«{pack}»',
                        what=f"The alignment contexts of the compiled functions of pack {pack[1:]}, their hint-only cells "
                             "fresh; their alignment follows from their pairings (`CoreMode/AlignOk/`).")
            + imports([m for f in fns for m in bases(f, pack)] + [glue_a(f['key']) for f in fns] + ['LeanVM.Guest.Bridge.ChkLit'])
            + 'set_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\n@[expose] public section\n\n'
            + ''.join(c for _, c in ctxs) + '\nend\n\nend LeanVM.Guest\n\n' + data.fn_thms(thms))


def cur_lit(c):
    return '[' + ', '.join(f'({a}, {b})' for a, b in c[0]) + f'], {c[1]}'


def render_win(pack, f):
    """A windowed function's context modules: its context (`Ctx`), and its checks but the pass (`Ok`); the pass is
    checked in windows from the core route's pairing states (`CoreMode/AlignOk/<fn>.lean`)."""
    k = f['key']
    base = f'LeanVM.Guest.Bridge.AlignCtx.«{k}»'
    cells, ctx = ctx_def(f)
    files = {}
    files[os.path.join(OUTW, k, 'Ctx.lean')] = (
        HEAD(mod=f'{base}.Ctx', what=f"`{k}`'s alignment check's context.")
        + imports(bases(f, pack) + [glue_a(k)]) + ns(k, f'''@[expose] public section

{ctx}end
'''))
    files[os.path.join(OUTW, k, 'Ok.lean')] = (
        HEAD(mod=f'{base}.Ok', what=f"`{k}`'s alignment check but the pass.")
        + imports([f'{base}.Ctx']) + ns(k, f'''public section

{cells_thm(f, cells)}
/-- `{k}`: the checks of its alignment but the pass's. -/
theorem alignPreOk : Bridge.alignPre alignCtx Fn.«{k}».advice = true := by
  decide +kernel

end
'''))
    return files


def cell_wins(key, pack):
    """The certificate's cell lists of a function, by name, with their cells."""
    blk = data.bundle_blocks()[key][1]
    text = blk + ''.join(data.read_text(p)
                         for p in sorted(glob.glob(os.path.join(data.ROOT, 'Pack', key, 'Cells*.lean'))))
    ds = defs(text)
    env = lambda n: parse(ds[n])
    cert = re.search(r'noncomputable def cert : Check\.Cert where\n(.*?)\n(?:/--|\Z)', blk, re.S).group(1)
    ws = parse(re.search(r'^  cells := (.*)$', cert, re.M).group(1))[1]
    return [(w[1], as_list(w, env)) for w in ws]


def pack_st(cs, j=0, acc=0):
    """`Bridge.packSt`: the chunks completed and where the packing stops."""
    out = []
    for c in cs:
        a = acc + (c << (20 * j))
        if j == 63:
            out.append(a)
            j, acc = 0, 0
        else:
            j, acc = j + 1, a
    return out, j, acc


def nums(l):
    return '[' + ', '.join(map(str, l)) + ']'


def render_sliced(pack, f, n):
    """A long function's context modules with its cells packed ahead (`alignCtxP`): its cells packed and their pieces,
    its context and its checks but the pass (`Ok`, with `alignCtxEq`); the pass is checked in windows from the core
    route's pairing states (`CoreMode/AlignOk/<fn>.lean`)."""
    k = f['key']
    base = f'LeanVM.Guest.Bridge.AlignCtx.«{k}»'
    files = {}
    pieces, cur, cnt = [], [], 0
    for name, cs in cell_wins(k, pack):
        cur.append((name, cs))
        cnt += len(cs)
        if cnt >= PIECE:
            pieces.append(cur)
            cur, cnt = [], 0
    if cur:
        pieces.append(cur)
    st, packs = (0, 0), []
    for pc in pieces:
        out, j, acc = pack_st([c for _, cs in pc for c in cs], *st)
        packs.append((pc, out, st, (j, acc)))
        st = (j, acc)
    packed = ''.join(f"/-- `{k}`: the chunks its cells' piece {m} completes. -/\ndef alignPack{m} : List ℕ :=\n  {nums(out)}\n\n"
                     for m, (_, out, _, _) in enumerate(packs))
    chain = ' ++ '.join([f'alignPack{m}' for m in range(len(packs))] + [f'[{st[1]}]'])
    files[os.path.join(OUTW, k, 'Packed.lean')] = (
        HEAD(mod=f'{base}.Packed', what=f"`{k}`'s cells packed (`Bridge.packGo`), piece by piece.")
        + imports(['LeanVM.Guest.Bridge.ProgAlSlice']) + ns(k, f'''@[expose] public section

{packed}/-- `{k}`: its cells packed. -/
def alignPacked : List ℕ :=
  {chain}

end
'''))
    piece = lambda pc: '(List.flatten [' + ', '.join(f'Fn.«{k}».{w}' for w, _ in pc) + '])'
    cells_mods = sorted(f'LeanVM.Guest.Pack.«{k}».{os.path.basename(p)[:-5]}'
                        for p in glob.glob(os.path.join(data.ROOT, 'Pack', k, 'Cells*.lean')))
    for m, (pc, out, a, b) in enumerate(packs):
        files[os.path.join(OUTW, k, f'Loc{m}.lean')] = (
            HEAD(mod=f'{base}.Loc{m}', what=f"`{k}`'s cells' piece {m}: its packing and its cells' width.")
            + imports([f'{base}.Packed'] + (cells_mods or [f'LeanVM.Guest.Pack.«{pack}».Bundle'])) + ns(k, f'''public section

/-- `{k}`: its cells' piece {m} packs from the state before it to the one after, its cells within `2^20`. -/
theorem alignLoc{m} :
    Bridge.packSt {piece(pc)} {a[0]} {a[1]} = (alignPack{m}, {b[0]}, {b[1]}) ∧
      {piece(pc)}.all (fun c ↦ Nat.blt c (2 ^ Bridge.cellBits)) = true := by
  decide +kernel

end
'''))
    cells, ctx = ctx_def(f)
    ctxp = ctx.split('\n', 1)[1].replace('noncomputable def alignCtx', 'noncomputable def alignCtxP').replace(
        f'Bridge.AlignCtx.ofData Fn.«{k}».cert.locs', 'Bridge.AlignCtx.ofPacked alignPacked true')
    files[os.path.join(OUTW, k, 'Ctx.lean')] = (
        HEAD(mod=f'{base}.Ctx', what=f"`{k}`'s alignment check's context, and with its cells packed.")
        + imports(bases(f, pack) + [f'{base}.Packed', glue_a(k)]) + ns(k, f'''@[expose] public section

{ctx}
/-- `{k}`: its context with its cells packed ahead. -/
{ctxp}end
'''))
    wl = ', '.join(f'Fn.«{k}».{w}' for pc in pieces for w, _ in pc)
    grp = ''.join(f'{piece(pc)} ++ (' for pc in pieces) + '[]' + ')' * len(pieces)
    pk = ', '.join(f'alignLoc{m}.1' for m in range(len(packs)))
    al = ', '.join(f'alignLoc{m}.2' for m in range(len(packs)))
    files[os.path.join(OUTW, k, 'Ok.lean')] = (
        HEAD(mod=f'{base}.Ok', what=f"`{k}`'s alignment check but the pass, and its context packed.")
        + imports([f'{base}.Ctx'] + [f'{base}.Loc{m}' for m in range(len(packs))])
        + ns(k, f'''public section

{cells_thm(f, cells)}
/-- `{k}`: the checks of its alignment but the pass's. -/
theorem alignPreOk : Bridge.alignPre alignCtxP Fn.«{k}».advice = true := by
  decide +kernel

/-- `{k}`: its cells, piece by piece. -/
theorem alignLocs : Fn.«{k}».cert.locs = {grp} := by
  show List.flatten [{wl}] = _
  simp only [List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

/-- `{k}`: its context is the one with its cells packed. -/
theorem alignCtxEq : alignCtx = alignCtxP := by
  have hp : Bridge.packGo Fn.«{k}».cert.locs 0 0 = alignPacked := by
    simp only [alignLocs, Bridge.packGo_append, {pk}, Bridge.packGo]
    simp only [alignPacked, List.append_assoc]
  have ha : Fn.«{k}».cert.locs.all (fun c ↦ Nat.blt c (2 ^ Bridge.cellBits)) = true := by
    simp only [alignLocs, List.all_append, {al}, List.all_nil, Bool.and_true]
  rw [alignCtx, alignCtxP, Bridge.ofData_eq_ofPacked, hp, ha]

end
'''))
    return files


def run(check):
    texts = data.core_texts()
    own = data.own_packs()
    core_pack = {k: bs[0][0] for k, bs in data.core_blocks().items() if bs[0][0] not in own and bs[0][1] == 'Core'}
    bundles = data.bundles()
    advice = data.advice()
    fns = functions()
    pows = pow_table()
    jt = jump_table(pows)
    entry_by_name = {F['name']: F['entry'] for F in fns.values()}
    key_by_name = {F['name']: k for k, F in fns.items()}
    packs, wins, fails = {}, [], []
    for key in sorted(texts):
        F, B = fns[key], bundles[key]
        A = advice.get(F['entry'])
        if A is None:
            raise SystemExit(f'align: {key} has no advice')
        body = body_of(texts[key])
        callees = sorted({s[1] if s[0] == 'call' else s[2] for s in walk_stmts(body) if s[0] in ('call', 'callIf')} |
                         {f for s in walk_stmts(body) if s[0] == 'dispatch' for f in s[2]})
        ents = {n: entry_by_name[n] for n in callees if n in entry_by_name}
        n = len(F['code'])
        cuts = list(range(0, n, WIN)) + [n] if n > WIN else []
        try:
            extra, states = align(F, body, A, B['locs'], B['plumb'], pows, jt, ents, cuts)
        except Fail as e:
            fails.append((key, str(e)))
            continue
        f = dict(key=key, j=A['j'], extra=extra, main=F['name'] == 'main', ents=sorted(ents.items()),
                 entk=[(n, key_by_name[n], bundles[key_by_name[n]]['pack']) for n in sorted(ents)],
                 core_pack=core_pack.get(key))
        if cuts:
            f['states'] = [states[c] for c in cuts]
            wins.append((B['pack'], f, n if n > SLICE else None))
        else:
            packs.setdefault(B['pack'], []).append(f)
    if fails:
        raise SystemExit('align: not aligned: ' + ', '.join(f'{k} ({r})' for k, r in fails))
    files = {os.path.join(OUT, f'{p}.lean'): render(p, fs) for p, fs in packs.items()}
    for p, f, n in wins:
        files.update(render_sliced(p, f, n) if n else render_win(p, f))
    existing = set(glob.glob(os.path.join(OUT, '*.lean'))) | set(glob.glob(os.path.join(OUTW, '*', '*.lean'))) | \
        set(glob.glob(os.path.join(OLDW, '*', '*.lean')))
    stale = genfiles.sync(data.quiet(files), existing, check)
    print(f'bridge-cert: {sum(len(v) for v in packs.values()) + len(wins)} of {len(texts)} functions align, '
          f'{len(wins)} in windows ({sum(1 for w in wins if w[2])} over slices), {len(files)} modules')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


def walk_stmts(block):
    for s in block:
        yield s
        if s[0] == 'ite':
            yield from walk_stmts(s[2])
            yield from walk_stmts(s[3])
        elif s[0] == 'match':
            for a in s[2]:
                yield from walk_stmts(a)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
