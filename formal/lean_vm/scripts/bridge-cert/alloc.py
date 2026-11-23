"""The allocation hints' check of every compiled function (`LeanVM/Guest/Bridge/AllocChk/*.lean`).

Per module of alignment checks `align.py` writes, each function's `Bridge.allocChk` over its alignment context,
plumbing, body, code and advice, by `decide +kernel`; per link module of `Guest/Checked`, each function's
`Bridge.AllocJ` (`Bridge.allocJ_of`, reusing the `Checked` and `ProgAl` link equations); and the assembly over every
function (`AllocChk/All.lean`). The check is mirrored here (`chk`), so that a function failing it fails here, naming
why. Run after `progal.py`; `--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/alloc.py [--check]
"""
import os, re, sys, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
import progal
import pair
import align

BR = os.path.join(data.ROOT, 'Bridge')
OUT = os.path.join(BR, 'AllocChk')
HEAD = genfiles.header('bridge-cert/alloc.py')
ALLOC = ('alloc', 'allocDyn', 'allocArm', 'allocFrames')


def check_module(ctx_mod):
    """The module of checks for the functions whose context `ctx_mod` holds."""
    return pair.check_module(ctx_mod).replace('.PairChk.', '.AllocChk.')


def is_alloc_atom(s):
    return s[0] == 'atom' and s[1] == 'hint' and s[2][0] in ('alloc', 'allocDyn')


def top_allocs(ss):
    return [s[2] for s in ss if is_alloc_atom(s)]


def no_alloc(s):
    if s[0] == 'atom':
        return not is_alloc_atom(s)
    if s[0] == 'ite':
        return all(no_alloc(x) for x in s[1]) and all(no_alloc(x) for x in s[2])
    if s[0] == 'match':
        return all(no_alloc(x) for a in s[1] for x in a)
    return True


def no_ret(s):
    if s[0] == 'ctl':
        return s[1] != 'ret'
    if s[0] == 'ite':
        return all(no_ret(x) for x in s[1]) and all(no_ret(x) for x in s[2])
    if s[0] == 'match':
        return all(no_ret(x) for a in s[1] for x in a)
    return True


def alloc_shape(ss):
    for i, s in enumerate(ss):
        if s[0] == 'atom':
            continue
        if not no_alloc(s) or not (not top_allocs(ss[i + 1:]) or no_ret(s)):
            return False
    return True


def cnt_alloc(ss):
    """`Bridge.cntL`: the allocation atoms of a block, nested ones included."""
    n = 0
    for s in ss:
        if is_alloc_atom(s):
            n += 1
        elif s[0] == 'ite':
            n += cnt_alloc(s[1]) + cnt_alloc(s[2])
        elif s[0] == 'match':
            n += sum(cnt_alloc(a) for a in s[1])
    return n


def matches(ss):
    """Every `match` of a block, nested ones included, as (selector, arm count)."""
    out = []
    for s in ss:
        if s[0] == 'ite':
            out += matches(s[2]) + matches(s[3])
        elif s[0] == 'match':
            out.append((s[1], len(s[2])))
            for a in s[2]:
                out += matches(a)
    return out


def is_loop(abody, name):
    """`Core.Fn.loop`: the body ends with a `callIf` to the function itself, then `ret []`."""
    return len(abody) >= 2 and abody[-1] == ('ret', []) and abody[-2][0] == 'callIf' and abody[-2][2] == name


def chk(F, body, abody, A, locs, extra, pows, jt, fs, loop):
    """`Bridge.curChk` and `Bridge.allocShape`/`pairsA`, mirrored: the reason each fails, or `None`."""
    entry, code, stat = F['entry'], F['code'], F['stat']
    loc = lambda v: extra[v] if v in extra else (locs[v] if v < len(locs) else 0)
    cell = lambda v: v in extra or (v < 1 << 30 and 2 <= loc(v) < fs)

    def pc_at(o):
        s = stat.get(o)
        return pows.get(s[1]) if s is not None and s[0] == 'k' and s[2] == 0 else None

    def zero_at(o):
        s = stat.get(o)
        return s is not None and s[0] == 'k' and s[1] == 0 and s[2] == 0

    def self_at(o):
        s = stat.get(o)
        return s is not None and ((s[0] == 'fpg' and s[1] == 0) or (s[0] == 'k' and s[1] == 1 and s[2] == 0 and F['main']))

    def next_at(o):
        s = stat.get(o)
        return s is not None and s[0] == 'fpg' and s[1] != 0
    hs = [(pc - A['entry'], h) for pc, l in A['hints'] for h in l]
    ptr = lambda h: h[1] if h[0] in ALLOC else None
    is_frame = lambda h: ptr(h) is not None and ptr(h) in F['sites']
    is_buf = lambda h: ptr(h) is not None and not is_frame(h)
    jumps = [i for i, c in enumerate(code) if c[0] == '.jump']

    def next_jump(a):
        return next((i for i in jumps if i >= a), len(code))
    frames = [(a, h) for a, h in hs if is_frame(h)]
    bs = [(a, h) for a, h in hs if is_buf(h)]
    pend = lambda off: any(a < off <= next_jump(a) for a, _ in frames)
    cur = None
    if cnt_alloc(body) > len(bs):
        cur = 'count'
    for i in jumps:
        oc, od, of = code[i][1]
        if not any(a > i for a, _ in bs) or (zero_at(oc) and of not in F['sites'] and not next_at(of)):
            continue
        t = pc_at(od)
        if not (self_at(of) and of not in F['sites'] and not (od == 0 and of == 1) and od not in F['arms']
                and t is not None and not any(i < a and entry + a < t for a, _ in bs)):
            cur = cur or 'jump before a buffer'
    for _, h in hs:
        if h[0] == 'frameAddress' and not (h[1] == fs and loop):
            cur = cur or 'frame address'
        if h[0] == 'cellAddress' and not (stat.get(h[1]) == ('fpg', h[2], 0) and h[2] < fs):
            cur = cur or 'cell address'
    seen = False
    for _, h in hs:
        if seen and is_buf(h):
            cur = cur or 'buffer after frame'
        seen = seen or is_frame(h)
    for a, h in frames:
        nj = next_jump(a)
        if h[0] not in ('alloc', 'allocArm', 'allocFrames') or nj >= len(code) or code[nj][1][2] != h[1]:
            cur = cur or 'frame'
            continue
        oc, od, q = code[nj][1]
        if zero_at(oc) or self_at(q) or next_at(q) or (od == 0 and q == 1):
            cur = cur or 'frame jump'
    if frames or F['sites']:
        for i in jumps:
            q = code[i][1][2]
            if q in F['sites'] and not any(h[1] == q and next_jump(a) == i for a, h in frames):
                cur = cur or 'site'
            if sum(1 for a, _ in frames if next_jump(a) == i) > 1:
                cur = cur or 'two frames'
        for i in jumps:
            t = pc_at(code[i][1][1])
            if t is not None and pend(max(t - entry, 0)):
                cur = cur or 'target'
        for x, n in matches(abody):
            for od, (sel, base) in F['arms'].items():
                if sel != x:
                    continue
                for k in range(n):
                    t = jt.get(base + k)
                    if t is not None and pend(max(t - entry, 0)):
                        cur = cur or 'arm target'
    if any(pend(max(s[3] - entry, 0)) for s in F['sites'].values()):
        cur = cur or 'return'
    if not alloc_shape(body):
        return cur, 'shape'
    atoms = top_allocs(body)
    if len(atoms) != len(bs):
        return cur, 'count'
    for c, (_, h) in zip(atoms, bs):
        if c[0] == 'alloc' and h[0] == 'alloc':
            ok = cell(c[1]) and loc(c[1]) == h[1] and c[2] == h[2]
        elif c[0] == 'allocDyn' and h[0] == 'allocDyn':
            ok = cell(c[1]) and cell(c[2]) and loc(c[1]) == h[1] and loc(c[2]) == h[2]
        elif c[0] == 'allocDyn' and h[0] == 'alloc':
            ok = cell(c[1]) and cell(c[2]) and loc(c[1]) == h[1] and pc_at(loc(c[2])) == h[2] and h[2] < 1 << 28
        else:
            ok = False
        if not ok:
            return cur, 'pair'
    return cur, None



# The frame hints' sizes (`Bridge.frChk`), mirrored to choose each function's listed callees.

def fr_vals(x):
    """The values of an atom's operand: a value, or a list of them."""
    if isinstance(x, tuple) and x[0] == 'list':
        return [v for y in x[1] for v in fr_vals(y)]
    try:
        return [data.val(x)]
    except (ValueError, IndexError, TypeError):
        return []


def fr_atom(e, env):
    h, a = data.head(e)
    if h == '.hint':
        return ('hint', data.core_hint(a[0], env))
    if h == '.const':
        w = a[1]
        return ('const', data.val(a[0]), (w[2][0], w[2][1]) if isinstance(w, tuple) and w[0] == 'app' else None)
    if h in ('.add', '.mul'):
        return (h[1:], data.val(a[0]), data.val(a[1]), data.val(a[2]))
    if h == '.load':
        return ('load', data.val(a[0]), data.val(a[1]), a[2])
    uses = []
    for x in a:
        if isinstance(x, tuple) and x[0] == 'id':
            try:
                x = env(x[1])
            except KeyError:
                continue
        uses += fr_vals(x)
    return ('other', h[1:], uses)


def fr_stmt(e, env):
    h, a = data.head(e)
    if h == '.atom':
        return ('atom', fr_atom(a[0], env))
    if h == '.ite':
        return ('ite', data.val(a[0]), fr_block(a[1], env), fr_block(a[2], env))
    if h == '.match_':
        return ('match', data.val(a[0]), [fr_block(x, env) for x in data.as_list(a[1], env)])
    if h == '.call':
        return ('call', a[0][1], data.vals(a[1], env), data.vals(a[2], env))
    if h == '.callIf':
        return ('callIf', data.val(a[0]), a[1][1], data.vals(a[2], env))
    if h == '.dispatch':
        return ('dispatch', data.val(a[0]), [x[1] for x in data.as_list(a[1], env)], data.vals(a[2], env),
                data.vals(a[3], env))
    if h == '.ret':
        return ('ret', data.vals(a[0], env))
    raise ValueError(h)


def fr_block(e, env):
    return [fr_stmt(x, env) for x in data.as_list(e, env)]


def fr_body(text):
    ds = data.defs(text[text.index('namespace core'):])
    cache = {}

    def env(n):
        if n not in cache:
            cache[n] = data.parse(ds[n])
        return cache[n]
    return fr_block(env('body'), env)


def fr_noret(ss):
    for s in ss:
        if s[0] == 'ret' or (s[0] == 'ite' and not (fr_noret(s[2]) and fr_noret(s[3]))) or \
                (s[0] == 'match' and not all(fr_noret(a) for a in s[2])):
            return False
    return True


def fr_spine(ss):
    """`Bridge.spine`."""
    out = []
    for s in ss:
        if s[0] == 'atom':
            out.append(s[1])
        elif s[0] in ('call', 'callIf', 'dispatch'):
            pass
        elif s[0] == 'ite' and fr_noret(s[2]) and fr_noret(s[3]):
            pass
        elif s[0] == 'match' and all(fr_noret(a) for a in s[2]):
            pass
        else:
            break
    return out


def fr_spine_named(ss):
    """`Bridge.spineNamed`: the returns of the calls on a block's spine."""
    out = []
    for s in ss:
        if s[0] == 'atom' or s[0] in ('callIf', 'dispatch'):
            pass
        elif s[0] == 'call':
            out += s[3]
        elif s[0] == 'ite' and fr_noret(s[2]) and fr_noret(s[3]):
            pass
        elif s[0] == 'match' and all(fr_noret(a) for a in s[2]):
            pass
        else:
            break
    return out


def fr_stmts(ss, sp, nm):
    """`Bridge.callsSpL`: each statement with the atoms and values on every path through it, each enclosing
    block's spine (`Bridge.spine`, `Bridge.spineNamed`)."""
    for s in ss:
        yield s, sp, nm
        if s[0] == 'ite':
            yield from fr_stmts(s[2], sp + fr_spine(s[2]), nm + fr_spine_named(s[2]))
            yield from fr_stmts(s[3], sp + fr_spine(s[3]), nm + fr_spine_named(s[3]))
        elif s[0] == 'match':
            for a in s[2]:
                yield from fr_stmts(a, sp + fr_spine(a), nm + fr_spine_named(a))


def fr_uses(a):
    """`atomUses`, as far as the check reads it."""
    if a[0] == 'const':
        return [a[1]]
    if a[0] in ('add', 'mul'):
        return [a[1], a[2], a[3]]
    if a[0] == 'load':
        return [a[1], a[2]]
    if a[0] == 'other':
        return a[2]
    if a[0] == 'hint':
        h = a[1]
        if h[0] == 'witness':
            d = h[2]
            return list(d[1]) if d[0] == 'stack' else [d[1]]
        if h[0] == 'alloc':
            return [h[1]]
        if h[0] == 'allocDyn':
            return [h[1], h[2]]
    return []


def fr_gpow(e):
    """`g^e` in `K`, `g = x` modulo `x^64 + x^4 + x^3 + x + 1`."""
    r, a = 1, 2
    while e:
        if e & 1:
            r = fr_kmul(r, a)
        a, e = fr_kmul(a, a), e >> 1
    return r


def fr_kmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> 64:
            a ^= (1 << 64) | 0b11011
    return r


def fr_const_ok(w, e):
    """`Memory.constOk`."""
    return e < 2 ** 20 and w == (fr_gpow(e), 0)


def fr_loop_tail(body, name, np, endc=None):
    """`(loopTail fn endc).isSome`."""
    if len(body) < 2 or body[-1] != ('ret', []) or body[-2][0] != 'callIf' or np < 1:
        return False
    _, c, g, args = body[-2]
    pre = body[:-2]
    if g != name or not args or args[1:] != list(range(1, np)):
        return False

    def defatom(d):
        for s in pre:
            if s[0] == 'atom' and s[1][0] in ('const', 'add', 'mul') and s[1][1] == d:
                return s[1]
        return None

    def is_step(d):
        a = defatom(d)
        if not a or a[0] != 'mul':
            return False
        isg = lambda z: (lambda b: b is not None and b[0] == 'const' and fr_const_ok(b[2], 1))(defatom(z))
        return (a[2] == 0 and isg(a[3])) or (a[3] == 0 and isg(a[2]))
    a = defatom(c)
    if not is_step(args[0]) or not a or a[0] != 'add':
        return False
    if endc is None:
        is_end = lambda y: np >= 2 and y == 1
    else:
        is_end = lambda y: (lambda b: b is not None and b[0] == 'const' and fr_const_ok(b[2], endc))(defatom(y))
    return (is_step(a[2]) and is_end(a[3])) or (is_step(a[3]) and is_end(a[2]))


def fr_end_of(body, name, np):
    """`Res.endOfFn`: `'param'` when the loop helper ends at its second parameter, else its constant end's exponent."""
    if fr_loop_tail(body, name, np):
        return 'param'
    return next((e for e in range(256) if fr_loop_tail(body, name, np, e)), None)


def fr_data(F, A, fb, np, locs, extra, fs, cal):
    """The listed callees of a function, as `Bridge.frChk` reads them, and the offsets of the frame hints it fails."""
    loc = lambda v: extra[v] if v in extra else (locs[v] if v < len(locs) else 0)
    cell = lambda v: v in extra or (v < 1 << 30 and 2 <= loc(v) < fs)
    frames = [(pc - A['entry'], h) for pc, l in A['hints'] for h in l if h[0] in ALLOC and h[1] in F['sites']]
    if not frames:
        return [], []
    def sp_const(v, e):
        return any(a[0] == 'const' and a[1] == v and fr_const_ok(a[2], e) for a in sp)

    def sp_word(v):
        return next((a[2] for a in sp if a[0] == 'const' and a[1] == v), None)

    def sp_eq_ptr(p, q):
        return p == q or any(a[0] == 'mul' and a[1] == p and any(
            c[0] == 'mul' and c[1] == q and c[2:] == a[2:] for c in sp) for a in sp)

    def sp_eq(x, y):
        return x == y or any(a[0] == 'load' and a[1] == x and any(
            c[0] == 'load' and c[1] == y and c[3] == a[3] and sp_eq_ptr(a[2], c[2]) for c in sp) for a in sp)

    def guard(b, a1, e):
        for a in sp:
            if a[0] == 'add' and a[1] == b:
                x, y = a[2], a[3]
                if (sp_const(x, e) and sp_eq(y, a1)) or (sp_const(y, e) and sp_eq(x, a1)):
                    return True
                wx, wy = sp_word(x), sp_word(y)
                if wx is not None and wy is not None and wx != wy:
                    return True
        return False
    cs, bad = set(), set()
    for st, sp, nm in fr_stmts(fb, fr_spine(fb), fr_spine_named(fb)):
        if st[0] not in ('call', 'callIf', 'dispatch'):
            continue
        args = st[2] if st[0] == 'call' else st[3]
        rets = st[3] if st[0] == 'call' else (st[4] if st[0] == 'dispatch' else [])
        for off, h in frames:
            site = F['sites'][h[1]]
            if list(site[0]) != list(args) or list(site[1]) != list(rets):
                continue
            ok = False
            if h[0] == 'alloc' and st[0] == 'call':
                c = cal(st[1])
                a0 = st[2][0] if st[2] else None
                ok = c is not None and ((c[1] == h[2] and not c[2]) or (c[2] and isinstance(c[4], int) and a0 is not None and (
                    (sp_const(a0, 0) and 0 < c[4] and (c[4] + 1) * c[1] == h[2]) or
                    (sp_const(a0, 1) and 1 < c[4] and c[4] * c[1] == h[2]))))
                if c:
                    cs.add(c[0])
            elif h[0] == 'allocArm' and st[0] == 'dispatch':
                x, sel, sizes = st[1], h[2], h[3]
                ok = loc(x) == sel and cell(x) and ((x < np and x not in extra) or any(x in fr_uses(a) for a in sp) or x in nm) and len(sizes) < 2 ** 28
                for i, f in enumerate(st[2]):
                    c = cal(f)
                    ok = ok and c is not None and i < len(sizes) and sizes[i] == c[1] and not c[2]
                    if c:
                        cs.add(c[0])
            elif h[0] == 'allocFrames' and st[0] == 'callIf' and len(st[3]) >= 2:
                size, stop = h[2], h[3]
                b, a0, a1 = st[1], st[3][0], st[3][1]
                c = cal(st[2])
                ok = c is not None and c[3] and c[1] == size and loc(a1) == stop and cell(a1) and \
                    ((sp_const(a0, 0) and guard(b, a1, 0)) or (sp_const(a0, 1) and guard(b, a1, 1)))
                if c:
                    cs.add(c[0])
            if not ok:
                bad.add(off)
    return sorted(cs), sorted(bad)


def run(check):
    ctxs, lk = progal.contexts(), progal.links()
    n = max(lk) + 1
    fns, adv, cores, bund = align.functions(), data.advice(), data.core_texts(), data.bundles()
    fss = {}
    for key, (_, blk) in data.bundle_blocks().items():
        fss[key] = int(re.search(r'^def fs : ℕ := (\d+)$', blk, re.M).group(1))
    pows = align.pow_table()
    jt = align.jump_table(pows)
    passed = {}
    fbs, byname, nps = {}, {}, {}
    for j, (k, _, _) in sorted(lk.items()):
        name = re.search(r'name := "([^"]*)"', cores[k]).group(1)
        fbs[k] = fr_body(cores[k])
        np_ = len(re.findall(r'\.n \d+', re.search(r'params := ([^\n]*)', cores[k]).group(1)))
        nps[k] = np_
        lpn = name.startswith('__loop')
        byname[name] = (j, fss[k], lpn, lpn and fr_loop_tail(fbs[k], name, np_), lpn and fr_end_of(fbs[k], name, np_))
    frd = {}
    for j, (k, _, _) in sorted(lk.items()):
        F = dict(fns[k], main=(j == 1))
        extra = {int(a): int(b) for a, b in re.findall(r'\((\d+), (\d+)\)', ctxs[k][0])}
        ab = align.body_of(cores[k])
        name = re.search(r'name := "([^"]*)"', cores[k]).group(1)
        cur, why = chk(F, data.body_of(cores[k]), ab, adv[F['entry']], bund[k]['locs'], extra,
                       pows, jt, fss[k], is_loop(ab, name))
        if cur:
            sys.exit(f'bridge-cert: `{k}` fails the bump pointer check: {cur}')
        if why:
            sys.exit(f'bridge-cert: `{k}` fails the allocation check: {why}')
        passed[j] = k
        frd[j] = fr_data(F, adv[F['entry']], fbs[k], nps[k], bund[k]['locs'], extra, fss[k], byname.get)
        if frd[j][1]:
            sys.exit(f'bridge-cert: `{k}` fails the frame sizes check at offsets {frd[j][1]}')
    files = {}
    shape_mods = {}
    body_mods = {}
    fr_mods = {}
    by_mod = {}
    for j, (k, _, _) in sorted(lk.items()):
        by_mod.setdefault(ctxs[k][2], []).append((j, k))
    for cm, jks in sorted(by_mod.items()):
        mod = check_module(cm)
        okp = os.path.join(data.LEAN_VM, *[x.strip('«»') for x in cm.split('.')]) + '.lean'
        win = cm.endswith('».Ok') and 'theorem alignCtxEq' in open(okp, encoding='utf-8').read()
        prf = 'rw [alignCtxEq]\n  decide +kernel' if win else 'decide +kernel'
        # the glue naming the functions' advice and their callees' indices
        imps = sorted(set(pair.pack_imports(cm)) | {align.glue_a(x) for j, k in jks for x in [k] + [lk[c][0] for c in frd[j][0]]})

        def shape(k):
            return [(k, 'allocShapeOk', 'Bridge.allocShape core.body = true', 'decide +kernel')]

        def ns(k, thms):
            return data.fn_thms(thms)

        def body_thm(j, k):
            return [(k, 'curBodyOk', f'Bridge.curBody alignCtx plumb core.body code.code Fn.«{k}».advice = true', prf)]

        def fr_thm(j, k):
            # the callees by their indices as the glue names them (`Fn.«k».idx`), not as numbers
            cs = '[' + ', '.join(f'Fn.«{lk[c][0]}».idx' for c in frd[j][0]) + ']'
            return [(k, 'frOk', f'Bridge.frChk alignCtx fs {cs} core.params core.body Fn.«{k}».advice = true', prf)]

        def thm(j, k):
            pre = [] if win else body_thm(j, k) + fr_thm(j, k)
            return (shape(k) if not win else []) + pre + [
                (k, 'allocOk', f'Bridge.allocRest alignCtx fs core.loop plumb core.body code.code Fn.«{k}».advice = true',
                 prf)]
        def thm1(j, k):
            # the common case in one command (`Bridge/ChkLit.lean`)
            if win or prf != 'decide +kernel': return thm(j, k)
            return ['alloc_chk%% «%s» [%s]\n' % (k, ', '.join('«%s»' % lk[c][0] for c in frd[j][0]))]
        body = data.fn_thms([t for j, k in jks for t in thm1(j, k)])
        files[os.path.join(OUT, mod.split('AllocChk.')[1].strip('«»') + '.lean')] = (
            HEAD(mod=mod, what="The kernel's checks that compiled functions' allocation hints pass the check.")
            + 'public import LeanVM.Guest.Bridge.AllocDefs\nimport all Statement.Data.AdviceHints\n'
            + ('' if win else 'public import LeanVM.Guest.Bridge.AllocFrDefs\npublic import LeanVM.Guest.Bridge.ChkLit\n')
            + f'public import {cm}\n'
            + ''.join(f'public import {m}\n' for m in imps)
            + '\n' + body.rstrip('\n') + '\n')
        if win:
            for j, k in jks:
                fmod = f'LeanVM.Guest.Bridge.AllocChk.«F_{k}»'
                fr_mods[k] = fmod
                files[os.path.join(OUT, f'F_{k}.lean')] = (
                    HEAD(mod=fmod, what=f"The kernel's check of `{k}`'s frame hints' sizes.")
                    + 'public import LeanVM.Guest.Bridge.AllocFrDefs\nimport all Statement.Data.AdviceHints\n'
                    + f'public import {cm}\n' + ''.join(f'public import {m}\n' for m in imps)
                    + '\n' + ns(k, fr_thm(j, k)).rstrip('\n') + '\n')
                bmod = f'LeanVM.Guest.Bridge.AllocChk.«B_{k}»'
                body_mods[k] = bmod
                files[os.path.join(OUT, f'B_{k}.lean')] = (
                    HEAD(mod=bmod, what=f"The kernel's check of `{k}`'s body for the bump pointer.")
                    + 'public import LeanVM.Guest.Bridge.AllocDefs\nimport all Statement.Data.AdviceHints\n' + f'public import {cm}\n'
                    + ''.join(f'public import {m}\n' for m in imps)
                    + '\n' + ns(k, body_thm(j, k)).rstrip('\n') + '\n')
                smod = f'LeanVM.Guest.Bridge.AllocChk.«S_{k}»'
                shape_mods[k] = smod
                files[os.path.join(OUT, f'S_{k}.lean')] = (
                    HEAD(mod=smod, what=f"The kernel's check that `{k}`'s body allocates its top-level allocation atoms on every path.")
                    + 'public import LeanVM.Guest.Bridge.AllocDefs\nimport all Statement.Data.AdviceHints\n'
                    + ''.join(f'public import {m}\n' for m in imps if m.endswith('.Core'))
                    + '\n' + ns(k, shape(k)).rstrip('\n') + '\n')
    groups = {}
    for j in sorted(lk):
        groups.setdefault(lk[j][1], []).append(j)
    fsq = set()
    for p in glob.glob(os.path.join(data.ROOT, 'Checked', 'Link*.lean')):
        fsq |= set(int(x) for x in re.findall(r'^kernel_rfl fsEq(\d+) ', open(p, encoding='utf-8').read(), re.M))
    for lmod, js in sorted(groups.items()):
        imps = {'LeanVM.Guest.Bridge.AllocLink', f'LeanVM.Guest.Checked.{lmod}', f'LeanVM.Guest.Bridge.ProgAl.Tab{lmod[len("Link"):]}'}  # the tables' entries, not the alignment checks
        imps |= {check_module(ctxs[lk[j][0]][2]) for j in js}
        imps |= {shape_mods[lk[j][0]] for j in js if lk[j][0] in shape_mods}
        imps |= {body_mods[lk[j][0]] for j in js if lk[j][0] in body_mods}
        imps |= {fr_mods[lk[j][0]] for j in js if lk[j][0] in fr_mods}
        body = []
        for j in js:
            k, _, hp = lk[j]
            pe = f'Checked.plumbEq{j}' if hp else f'Bridge.ProgAl.plumbEq{j}'
            fe = f'Checked.fsEq{j}'
            if j not in fsq:
                body.append(f'kernel_rfl fsEq{j} : B2C.fsN {j} = Fn.«{k}».fs\n')
                fe = f'fsEq{j}'
            body.append(f'theorem fok{j} : Bridge.FrJ {j} := Bridge.frJ_of Checked.code{j} Checked.core{j} Checked.cert{j} {pe} '
                        f'Bridge.ProgAl.tab{j} rfl {fe} Fn.«{k}».frOk\n')
            body.append(f'theorem aok{j} : Bridge.AllocJ {j} := Bridge.allocJ_of Checked.code{j} Checked.core{j} '
                        f'Checked.cert{j} {pe} Bridge.ProgAl.tab{j} rfl {fe} Fn.«{k}».allocShapeOk Fn.«{k}».curBodyOk '
                        f'Fn.«{k}».allocOk\n')
        files[os.path.join(OUT, f'{lmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.AllocChk.{lmod}',
                        what=f"The functions of `Checked.{lmod}` pass the allocation hints' check over their alignment's context.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '''meta import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Bridge.AllocChk

open LeanVM.Guest

public section

''' + ''.join(body) + '''
end

end LeanVM.Guest.Bridge.AllocChk
''')
    pred = 'fun j ↦ Bridge.AllocJ j'
    step = 256
    parts = [(lo, min(lo + step, n)) for lo in range(1, n, step)]
    thms = ''.join(f'''theorem allocJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.AllocJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := {pred}) {la} {lb} aok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    top = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(allocJ_{a} j {la} {lb})')
    fpred = 'fun j ↦ Bridge.FrJ j'
    fthms = ''.join(f'''theorem frJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.FrJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := {fpred}) {la} {lb} fok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    ftop = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(frJ_{a} j {la} {lb})')
    files[os.path.join(OUT, 'All.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.AllocChk.All',
                    what="Every compiled function's allocation hints pass the check.")
        + 'public import LeanVM.Guest.Glob\n'
        + ''.join(f'public import LeanVM.Guest.Bridge.AllocChk.{m}\n' for m in sorted(groups)) + f'''
namespace LeanVM.Guest.Bridge.AllocChk

open LeanVM.Guest

public section

{thms}/-- **Every compiled function's allocation hints pass the check.** -/
theorem allocJ_all : ∀ j, 1 ≤ j → j < {n} → Bridge.AllocJ j := fun j h1 h2 ↦
  {top}

/-- **Every compiled function's allocation hints pass the bump pointer's check.** -/
theorem curJ_all : ∀ j, 1 ≤ j → j < {n} → Bridge.CurJ j := fun j h1 h2 ↦
  Bridge.curJ_of_allocJ (allocJ_all j h1 h2)

{fthms}/-- **Every compiled function's frame hints pass the sizes check.** -/
theorem frJ_all : ∀ j, 1 ≤ j → j < {n} → Bridge.FrJ j := fun j h1 h2 ↦
  {ftop}

end

end LeanVM.Guest.Bridge.AllocChk
''')
    existing = set(glob.glob(os.path.join(OUT, '*.lean')))
    stale = genfiles.sync(files, existing, check)
    print(f'bridge-cert: the allocation hints of {len(passed)} functions over {len(groups)} link modules')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
