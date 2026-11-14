"""The hint bridge's alignment checks (`LeanVM/Guest/Bridge/Align/*.lean`, `AlignWin/*/*.lean`).

The pass mirrors `Bridge.alignOk` (`LeanVM/Guest/Bridge/AlignDefs.lean`) over the generated data: a forward
walk over each function's code pairing its flow hints, branches, table jumps, call sites and returns with
body positions (zippers into the body), finding the cells only hints touch as `gen.py` does. It writes, per
pack of the bundles, each function's context and the kernel's checks; a function longer than `WIN`
instructions is checked in windows, the pass's state named at each window's end (`Bridge.KSt`), a module
per window and one chaining them (`Bridge.alignOk_of_chain`). `--check` writes nothing and fails when a
file is stale.

    python3 -I scripts/bridge-cert/align.py [--check]
"""
import os, sys, glob, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import data
from data import parse, as_list, head, defs

OUT = os.path.join(data.ROOT, 'Bridge', 'Align')
# Not yet within the module budget: `main_loop2`'s context (120,769 cells) and windows.
SKIP = {'main_loop2'}
FUEL = 1 << 20
HALT = (1 << 19) - 1


def stmt(e, env):
    h, a = head(e)
    if h == '.atom':
        ah, aa = head(a[0])
        return ('hint', data.core_hint(aa[0], env)) if ah == '.hint' else ('atom', ah[1:])
    if h == '.ite':
        return ('ite', data.val(a[0]), block(a[1], env), block(a[2], env))
    if h == '.match_':
        return ('match', data.val(a[0]), [block(x, env) for x in as_list(a[1], env)])
    if h == '.call':
        return ('call', a[0][1], data.vals(a[1], env), data.vals(a[2], env))
    if h == '.callIf':
        return ('callIf', data.val(a[0]), a[1][1], data.vals(a[2], env))
    if h == '.dispatch':
        return ('dispatch', data.val(a[0]), None, data.vals(a[2], env), data.vals(a[3], env))
    if h == '.ret':
        return ('ret', data.vals(a[0], env))
    raise ValueError(h)


def block(e, env):
    return [stmt(x, env) for x in as_list(e, env)]


def body_of(text):
    ds = defs(text[text.index('namespace core'):])
    cache = {}

    def env(n):
        if n not in cache:
            cache[n] = parse(ds[n])
        return cache[n]
    return block(env('body'), env)


def functions():
    """Each compiled function's name, entry, code with operands and plumbing, by stable name."""
    out = {}
    for b in sorted(glob.glob(data.ROOT + '/Pack/*/Bundle.lean')):
        t = open(b, encoding='utf-8').read()
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.')[1:]:
            key = blk.split('\n', 1)[0].strip().strip('«»')
            ds = defs(blk)
            cache = {}

            def env(n, ds=ds, cache=cache):
                if n not in cache:
                    cache[n] = parse(ds[n])
                return cache[n]
            cm = re.search(r'def code : CompiledFunction :=\s*⟨"([^"]*)", (\d+), (\d+), \[([^\]]*)\]⟩', blk)
            code = [head(x) for c in cm.group(4).split(',') if c.strip() for x in as_list(env(c.strip()), env)]
            stat, sites, arms, chains = {}, [], [], []
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
            out[key] = dict(name=cm.group(1), entry=int(cm.group(2)), code=code, stat=stat, sites=by_q, arms=by_od)
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
    next_ = lambda o: st(o) is not None and st(o)[0] == 'fpg' and st(o)[1] != 0

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
        from gen import need
        n = need(c, h)
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
    from gen import FLOW
    return FLOW


WIN = 4096
OUTW = os.path.join(data.ROOT, 'Bridge', 'AlignWin')
HEAD = '/-\n  {mod}\n\n  Generated by `scripts/bridge-cert/align.py`; do not edit.\n  {what}\n-/\n\nmodule\n\n'


def ctx_def(f):
    k = f['key']
    cells = '[' + ', '.join(f'({v}, {c})' for v, c in f['extra']) + ']'
    ents = '[' + ', '.join(f'("{n}", {e})' for n, e in f['ents']) + ']'
    return cells, f'''/-- `{k}`: what its alignment check reads beyond its body and code. -/
noncomputable def alignCtx : Bridge.AlignCtx :=
  Bridge.AlignCtx.ofData Fn.«{k}».cert.locs {cells} Fn.«{k}».code.entryPc {"true" if f["main"] else "false"}
    Fn.«{k}».plumb Data.powTree Data.jtTrie {ents} {HALT} Fn.«{k}».code.instructionCount
'''


def cells_thm(f, cells):
    k = f['key']
    return f'''/-- `{k}`: its hint-only cells are fresh. -/
theorem alignCellsOk :
    Bridge.cellsFresh Fn.«{k}».cert.locs (Bridge.plumbCells Fn.«{k}».plumb) {cells} = true := by
  decide +kernel
'''


def bases(f, pack):
    from gen import core_module
    return ['LeanVM.Guest.Bridge.AlignDefs', 'LeanVM.Guest.Data.AdviceHints', 'LeanVM.Guest.Data.Pows',
            f'LeanVM.Guest.Pack.«{pack}».Bundle',
            f'LeanVM.Guest.Pack.«{f["core_pack"]}».Core' if f['core_pack'] else core_module(f['key'])]


def imports(ms):
    return ''.join(f'public import {m}\n' for m in sorted(set(ms))) + '\n'


def ns(k, body):
    return f'namespace LeanVM.Guest.Fn.«{k}»\n\nopen LeanVM.Guest\n\n{body}\nend LeanVM.Guest.Fn.«{k}»\n'


def render(pack, fns):
    out = [HEAD.format(mod=f'LeanVM.Guest.Bridge.Align.«{pack}»',
                       what=f"The kernel's checks that compiled functions of pack {pack[1:]} align with their bodies."),
           imports(m for f in fns for m in bases(f, pack))]
    for f in fns:
        k = f['key']
        cells, ctx = ctx_def(f)
        out.append(ns(k, f'''@[expose] public section

{ctx}
end

public section

{cells_thm(f, cells)}
/-- `{k}` aligns with its body. -/
theorem alignOk :
    Bridge.alignOk alignCtx Fn.«{k}».core.body Fn.«{k}».code.code Data.adviceFn{f["j"]} = true := by
  decide +kernel

end
'''))
    return '\n'.join(out)


def cur_lit(c):
    return '[' + ', '.join(f'({a}, {b})' for a, b in c[0]) + f'], {c[1]}'


def kst(K):
    i, nd, cur, pend, tabs = K
    c = 'none' if cur is None else f'some ({cur_lit(cur)})'
    pe = '[' + ', '.join(f'({o}, ({cur_lit(z)}))' for o, z in pend) + ']'
    ta = '[' + ', '.join(f'({b}, ({cur_lit(z)}), {m})' for b, z, m in tabs) + ']'
    return f'⟨{i}, {nd}, {c}, {pe}, {ta}⟩'


def render_win(pack, f):
    """A windowed function's modules: its context and named states, one per window, and the chain."""
    k = f['key']
    base = f'LeanVM.Guest.Bridge.AlignWin.«{k}»'
    ks = f['states']
    cells, ctx = ctx_def(f)
    args = f'alignCtx Fn.«{k}».core.body Fn.«{k}».code.code Data.adviceFn{f["j"]}'
    defs = ''.join(f'/-- `{k}`: the pass\'s state at offset {K[0]}. -/\ndef alignK{n} : Bridge.KSt :=\n  {kst(K)}\n\n'
                   for n, K in enumerate(ks))
    files = {}
    files[os.path.join(OUTW, k, 'Ctx.lean')] = (
        HEAD.format(mod=f'{base}.Ctx', what=f"`{k}`'s alignment check's context and the pass's states at its windows' ends.")
        + imports(bases(f, pack)) + ns(k, f'''@[expose] public section

{ctx}
{defs}end
'''))
    files[os.path.join(OUTW, k, 'Pre.lean')] = (
        HEAD.format(mod=f'{base}.Pre', what=f"`{k}`'s alignment check but the pass.")
        + imports([f'{base}.Ctx']) + ns(k, f'''public section

{cells_thm(f, cells)}
/-- `{k}`: the checks of its alignment but the pass's. -/
theorem alignPreOk : Bridge.alignPre alignCtx Data.adviceFn{f["j"]} = true := by
  decide +kernel

/-- `{k}`: the pass's last state is at the end. -/
theorem alignEndOk : Bridge.chainEnd Fn.«{k}».code.code alignK{len(ks) - 1} = true := by
  decide +kernel

end
'''))
    for n in range(len(ks) - 1):
        files[os.path.join(OUTW, k, f'W{n}.lean')] = (
            HEAD.format(mod=f'{base}.W{n}', what=f"`{k}`'s alignment pass from offset {ks[n][0]} to {ks[n + 1][0]}.")
            + imports([f'{base}.Ctx']) + ns(k, f'''public section

/-- `{k}`: the pass from offset {ks[n][0]} to {ks[n + 1][0]}. -/
theorem alignWin{n} : Bridge.winOk {args} alignK{n} alignK{n + 1} = true := by
  decide +kernel

end
'''))
    chain = 'alignEndOk'
    for n in reversed(range(len(ks) - 1)):
        chain = f'(And.intro alignWin{n} {chain})'
    files[os.path.join(OUTW, k, 'Ok.lean')] = (
        HEAD.format(mod=f'{base}.Ok', what=f"`{k}` aligns with its body, by its windows.")
        + imports(['LeanVM.Guest.Bridge.AlignRun', f'{base}.Pre'] + [f'{base}.W{n}' for n in range(len(ks) - 1)]) + ns(k, f'''public section

/-- `{k}` aligns with its body. -/
theorem alignOk : Bridge.alignOk {args} = true :=
  Bridge.alignOk_of_chain alignPreOk (ks := [{', '.join(f'alignK{n}' for n in range(1, len(ks)))}])
    {chain}

end
'''))
    return files


def run(check):
    texts = data.core_texts()
    core_pack = {}
    for p in sorted(glob.glob(data.ROOT + '/Pack/P[0-9]*/Core.lean')):
        for m in re.finditer(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', open(p, encoding='utf-8').read(), re.M):
            core_pack[m.group(1)] = p.split('/')[-2]
    bundles = data.bundles()
    advice = data.advice()
    fns = functions()
    pows = pow_table()
    jt = jump_table(pows)
    entry_by_name = {F['name']: F['entry'] for F in fns.values()}
    packs, wins, fails = {}, [], []
    for key in sorted(texts):
        if key in SKIP:
            continue
        F, B = fns[key], bundles[key]
        A = advice.get(F['entry'])
        if A is None:
            raise SystemExit(f'align: {key} has no advice')
        body = body_of(texts[key])
        callees = sorted({s[1] if s[0] == 'call' else s[2] for s in walk_stmts(body) if s[0] in ('call', 'callIf')})
        ents = {n: entry_by_name[n] for n in callees if n in entry_by_name}
        n = len(F['code'])
        cuts = list(range(0, n, WIN)) + [n] if n > WIN else []
        try:
            extra, states = align(F, body, A, B['locs'], B['plumb'], pows, jt, ents, cuts)
        except Fail as e:
            fails.append((key, str(e)))
            continue
        f = dict(key=key, j=A['j'], extra=extra, main=F['name'] == 'main', ents=sorted(ents.items()),
                 core_pack=core_pack.get(key))
        if cuts:
            f['states'] = [states[c] for c in cuts]
            wins.append((B['pack'], f))
        else:
            packs.setdefault(B['pack'], []).append(f)
    if fails:
        raise SystemExit('align: not aligned: ' + ', '.join(f'{k} ({r})' for k, r in fails))
    files = {os.path.join(OUT, f'{p}.lean'): render(p, fs) for p, fs in packs.items()}
    for p, f in wins:
        files.update(render_win(p, f))
    stale = []
    existing = set(glob.glob(os.path.join(OUT, '*.lean'))) | set(glob.glob(os.path.join(OUTW, '*', '*.lean')))
    for path, text in sorted(files.items()):
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if old != text:
            stale.append(path)
            if not check:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                open(path, 'w', encoding='utf-8').write(text)
    for path in sorted(existing - set(files)):
        stale.append(path)
        if not check:
            os.remove(path)
    if not check:
        for d in glob.glob(os.path.join(OUTW, '*')):
            if os.path.isdir(d) and not os.listdir(d):
                os.rmdir(d)
    print(f'bridge-cert: {sum(len(v) for v in packs.values()) + len(wins)} of {len(texts)} functions align, '
          f'{len(wins)} in windows, {len(files)} modules; skipped: {", ".join(sorted(SKIP))}')
    if check and stale:
        for p in stale:
            print(f'stale: {os.path.relpath(p, data.LEAN_VM)}', file=sys.stderr)
        sys.exit(1)


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
