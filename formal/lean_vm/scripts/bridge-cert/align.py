"""The hint bridge's alignment pass over the generated data, mirroring `Bridge.alignOk`
(`LeanVM/Guest/Bridge/AlignDefs.lean`): a forward walk over each function's code pairing its flow hints,
branches, table jumps, call sites and returns with body positions (cursors into the body), finding the
cells only hints touch as `gen.py` does. It prints which functions align. `--emit` also writes, per pack,
each aligning function's context and the kernel's checks (`LeanVM/Guest/Bridge/Align/*.lean`); those
checks are not yet within the module budget, so they are not part of the tree.

    python3 -I scripts/bridge-cert/align.py [--emit]
"""
import os, sys, glob, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import data
from data import parse, as_list, head, defs

OUT = os.path.join(data.ROOT, 'Bridge', 'Align')
FUEL = 1 << 20
HALT = (1 << 19) - 1
SKIP = {'main_loop2'}


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
            stat, sites, arms = {}, [], []
            pl = re.search(r'noncomputable def plumb : B2C\.Plumb where\n(.*?)\n(?:/--|\Z)', blk, re.S)
            if pl:
                pt = pl.group(1)
                st = re.search(r'^  stat := (.*)$', pt, re.M)
                if st:
                    for m in re.finditer(r'\((\d+), \(\.(k|fpg) (\d+)(?: (\d+))?\)\)', st.group(1)):
                        stat.setdefault(int(m.group(1)), (m.group(2), int(m.group(3)), int(m.group(4) or 0)))
                si = re.search(r'^  sites := (.*)$', pt, re.M)
                if si:
                    for m in re.finditer(r'⟨\[([^\]]*)\], \[([^\]]*)\], (\d+), (\d+), (\d+)⟩', si.group(1)):
                        nums = lambda s: [int(x) for x in s.split(',') if x.strip()]
                        sites.append((nums(m.group(1)), nums(m.group(2)), int(m.group(3)), int(m.group(4)),
                                      int(m.group(5))))
                ar = re.search(r'^  arms := (.*)$', pt, re.M)
                if ar:
                    arms = [tuple(int(x) for x in m.groups()) for m in re.finditer(r'\((\d+), (\d+), (\d+)\)', ar.group(1))]
            out[key] = dict(name=cm.group(1), entry=int(cm.group(2)), code=code, stat=stat, sites=sites, arms=arms)
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


def block_at(body, up):
    b = body
    for k, c in reversed(up):
        b = sub_block(b[k], c) if k < len(b) else []
    return b


def pos_of(body, up, k):
    out = list(block_at(body, up)[k:])
    for i in range(len(up)):
        kk, _ = up[i]
        out += block_at(body, up[i + 1:])[kk + 1:]
    return out


def norm(body, up, k):
    while True:
        b = block_at(body, up)
        if k < len(b):
            if b[k][0] == 'hint' and not flow_atom(b[k]):
                k += 1
                continue
            if b[k][0] == 'atom':
                k += 1
                continue
            return (up, k)
        if not up:
            return (up, k)
        (kk, _), up = up[0], up[1:]
        k = kk + 1


class Fail(Exception):
    pass


def align(F, body, A, locs, plumb_cells, pows, jt, ents):
    """The alignment pass; the hint-only cells, or `Fail`."""
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

    def site(args, rets):
        return next((s for s in F['sites'] if s[0] == args and s[1] == rets), None)

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

    def jump(i, oc, od, of, up, k):
        if zero(oc):
            return (up, k), []
        t = pc_at(od)
        if nz(oc) and self_(of) and t is not None and entry + i < t < entry + len(code):
            return None, [(t - entry, (up, k))]
        b = block_at(body, up)
        s = b[k] if k < len(b) else None
        after = lambda: norm(body, up, k + 1)
        if s is None:
            raise Fail(f'jump at {i} past the body')
        if s[0] == 'ite':
            if loc(s[1]) != oc or not self_(of):
                raise Fail(f'ite at {i}')
            return norm(body, [(k, 0)] + up, 0), [(fwd(i, t), norm(body, [(k, 1)] + up, 0))]
        if s[0] == 'match':
            a = next((a for a in F['arms'] if a[0] == s[1] and a[1] == od), None)
            if not self_(of) or a is None:
                raise Fail(f'match at {i}')
            return None, [(fwd(i, jt.get(a[2] + j)), norm(body, [(k, j)] + up, 0)) for j in range(len(s[2]))]
        if s[0] == 'call':
            si = site(s[2], s[3])
            if si is None or si[2] != of or t is None or ents.get(s[1]) != t:
                raise Fail(f'call at {i}')
            return None, [(fwd(i, si[3]), after())]
        if s[0] == 'callIf':
            if loc(s[1]) != oc or t is None or ents.get(s[2]) != t:
                raise Fail(f'callIf at {i}')
            ca = after()
            if next_(of):
                if pos_of(body, *ca) != [('ret', [])]:
                    raise Fail(f'tail at {i}')
                return ca, []
            si = site(s[3], [])
            if si is None or si[2] != of or si[3] != entry + i + 1:
                raise Fail(f'callIf site at {i}')
            return ca, []
        if s[0] == 'dispatch':
            si = site(s[3], s[4])
            if si is None or si[2] != of or si[4] != od:
                raise Fail(f'dispatch at {i}')
            return None, [(fwd(i, si[3]), after())]
        if s[0] == 'ret':
            if (main and self_(of) and t == HALT) or (not main and od == 0 and of == 1):
                return None, []
            raise Fail(f'ret at {i}')
        raise Fail(f'jump at {i} on {s[0]}')

    pcs = [pc for pc, _ in A['hints']]
    if A['entry'] != entry or any(x >= y for x, y in zip(pcs, pcs[1:])) or any(x < entry for x in pcs):
        raise Fail('advice not by increasing pc from the entry')
    hints = dict(A['hints'])
    cur, pend = ([], 0), []
    for i, (op, a) in enumerate(code):
        here = [p for p in pend if p[0] == i]
        pend = [p for p in pend if p[0] != i]
        c = cur if cur is not None else (here[0][1] if here else None)
        if c is None:
            continue
        if any(p[1] != c for p in here):
            raise Fail(f'join at {i}')
        up, k = norm(body, *c)
        for h in hints.get(entry + i, []):
            if h[0] not in data_flow():
                continue
            b = block_at(body, up)
            if not (k < len(b) and b[k][0] == 'hint'):
                raise Fail(f'hint {h[0]} at {i} without its atom')
            compiles(b[k][1], h)
            up, k = norm(body, up, k + 1)
        if op == '.jump':
            cur, tg = jump(i, a[0], a[1], a[2], up, k)
        else:
            cur, tg = (up, k), []
        pend += tg
    if cur is not None or pend:
        raise Fail('falls off the end')
    return sorted(extra.items())


def data_flow():
    from gen import FLOW
    return FLOW


def render(pack, fns):
    from gen import core_module
    imports = ['LeanVM.Guest.Bridge.AlignDefs', 'LeanVM.Guest.Data.AdviceHints', 'LeanVM.Guest.Data.Pows',
               f'LeanVM.Guest.Pack.«{pack}».Bundle']
    imports += sorted({f'LeanVM.Guest.Pack.«{f["core_pack"]}».Core' if f['core_pack'] else core_module(f['key'])
                       for f in fns})
    imports = sorted(set(imports))
    out = [f'/-\n  LeanVM.Guest.Bridge.Align.«{pack}»\n\n  Generated by `scripts/bridge-cert/align.py`; do not edit.\n'
           f'  The kernel\'s checks that compiled functions of pack {pack[1:]} align with their bodies.\n-/\n',
           'module\n']
    out.append(''.join(f'public import {m}\n' for m in imports))
    for f in fns:
        k = f['key']
        cells = '[' + ', '.join(f'({v}, {c})' for v, c in f['extra']) + ']'
        ents = '[' + ', '.join(f'("{n}", {e})' for n, e in f['ents']) + ']'
        out.append(f'''namespace LeanVM.Guest.Fn.«{k}»

open LeanVM.Guest

@[expose] public section

/-- `{k}`: what its alignment check reads beyond its body and code. -/
noncomputable def alignCtx : Bridge.AlignCtx :=
  ⟨Fn.«{k}».cert.locs, {cells}, Fn.«{k}».code.entryPc, {"true" if f["main"] else "false"}, Fn.«{k}».plumb.stat,
    Fn.«{k}».plumb.sites, Fn.«{k}».plumb.arms, Data.powTree, Data.jtTrie, {ents}, {HALT},
    Fn.«{k}».code.instructionCount, {FUEL}⟩

end

public section

/-- `{k}`: its hint-only cells are fresh. -/
theorem alignCellsOk :
    Bridge.cellsFresh Fn.«{k}».cert.locs (Bridge.plumbCells Fn.«{k}».plumb) {cells} = true := by
  decide +kernel

/-- `{k}` aligns with its body. -/
theorem alignOk :
    Bridge.alignOk alignCtx Fn.«{k}».core.body Fn.«{k}».code.code Data.adviceFn{f["j"]} = true := by
  decide +kernel

end

end LeanVM.Guest.Fn.«{k}»
''')
    return '\n'.join(out)


def run(check, emit=True):
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
    packs, fails = {}, []
    for key in sorted(texts):
        if key in SKIP:
            fails.append((key, 'skipped'))
            continue
        F, B = fns[key], bundles[key]
        A = advice.get(F['entry'])
        body = body_of(texts[key])
        callees = sorted({s[1] if s[0] == 'call' else s[2] for s in walk_stmts(body) if s[0] in ('call', 'callIf')})
        ents = {n: entry_by_name[n] for n in callees if n in entry_by_name}
        try:
            extra = align(F, body, A, B['locs'], B['plumb'], pows, jt, ents)
        except Fail as e:
            fails.append((key, str(e)))
            continue
        packs.setdefault(B['pack'], []).append(dict(key=key, j=A['j'] if A else None, extra=extra,
                                                    main=F['name'] == 'main', ents=sorted(ents.items()),
                                                    core_pack=core_pack.get(key)))
    for p in packs.values():
        if any(f['j'] is None for f in p):
            raise SystemExit('align: a function without advice')
    files = {os.path.join(OUT, f'{p}.lean'): render(p, fs) for p, fs in packs.items()} if emit else {}
    stale = []
    existing = set(glob.glob(os.path.join(OUT, '*.lean'))) if emit else set()
    for path, text in sorted(files.items()):
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if old != text:
            stale.append(path)
            if not check:
                os.makedirs(OUT, exist_ok=True)
                open(path, 'w', encoding='utf-8').write(text)
    for path in sorted(existing - set(files)):
        stale.append(path)
        if not check:
            os.remove(path)
    n = sum(len(v) for v in packs.values())
    print(f'bridge-cert: {n} of {len(texts)} functions align, {len(files)} modules; not: '
          + ', '.join(f'{k} ({r})' for k, r in fails))
    return stale


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
    run(False, '--emit' in sys.argv[1:])
