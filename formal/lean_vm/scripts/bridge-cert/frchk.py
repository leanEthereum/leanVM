"""The frame hints' sizes (`Bridge.frChk`), mirrored to choose each function's listed callees and name a failing
one (`alloc.py` writes the kernel's check). Restored from the tag's `alloc.py` on the current parse
(`data.core_fn`)."""
import re
import data

FRAME = ('alloc', 'allocArm', 'allocFrames')


def noret(ss):
    for s in ss:
        if s[0] == 'ret' or (s[0] == 'ite' and not (noret(s[2]) and noret(s[3]))) or \
                (s[0] == 'match' and not all(noret(a) for a in s[2])):
            return False
    return True


def spine(ss):
    """`Bridge.spine`: the atoms of a block before its first statement that may return."""
    out = []
    for s in ss:
        if s[0] == 'a':
            out.append(s[1])
        elif s[0] in ('call', 'callIf', 'dispatch'):
            pass
        elif s[0] == 'ite' and noret(s[2]) and noret(s[3]):
            pass
        elif s[0] == 'match' and all(noret(a) for a in s[2]):
            pass
        else:
            break
    return out


def spine_named(ss):
    """`Bridge.spineNamed`: the returns of the calls on a block's spine."""
    out = []
    for s in ss:
        if s[0] in ('a', 'callIf', 'dispatch'):
            pass
        elif s[0] == 'call':
            out += s[3]
        elif s[0] == 'ite' and noret(s[2]) and noret(s[3]):
            pass
        elif s[0] == 'match' and all(noret(a) for a in s[2]):
            pass
        else:
            break
    return out


def stmts(ss, sp, nm):
    """`Bridge.callsSpL`: each statement with the atoms and values on every path through it."""
    for s in ss:
        yield s, sp, nm
        if s[0] == 'ite':
            yield from stmts(s[2], sp + spine(s[2]), nm + spine_named(s[2]))
            yield from stmts(s[3], sp + spine(s[3]), nm + spine_named(s[3]))
        elif s[0] == 'match':
            for a in s[2]:
                yield from stmts(a, sp + spine(a), nm + spine_named(a))


def uses(a):
    """`atomUses`, as far as the check reads it (a hint's: its allocation's values only)."""
    k = a[0]
    if k == 'const':
        return [a[1]]
    if k in ('add', 'mul'):
        return [a[1], a[2], a[3]]
    if k in ('copy', 'load', 'assertEq', 'assertInK', 'touch'):
        return [a[1], a[2]] if k != 'touch' else [a[2]]
    if k == 'assertNe':
        return [a[1], a[2], a[3]]
    if k == 'rangeCheck':
        return [a[1], a[2], a[5]]
    if k == 'keccak':
        return list(a[1]) + list(a[2])
    if k == 'frameAddr':
        return [a[1]] + list(a[2])
    if k == 'hint' and a[1][0] in ('alloc', 'allocDyn'):
        return [x for x in a[1][1:] if isinstance(x, int)][:1 if a[1][0] == 'alloc' else 2]
    return []


def kmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> 64:
            a ^= (1 << 64) | 0b11011
    return r


def gpow(e):
    r, a = 1, 2
    while e:
        if e & 1:
            r = kmul(r, a)
        a, e = kmul(a, a), e >> 1
    return r


def const_ok(w, e):
    """`Memory.constOk`."""
    return w is not None and e < 2 ** 20 and tuple(w) == (gpow(e), 0)


def loop_tail(body, name, np, endc=None):
    """`(loopTail fn endc).isSome`."""
    if len(body) < 2 or body[-1] != ('ret', []) or body[-2][0] != 'callIf' or np < 1:
        return False
    _, c, g, args = body[-2]
    pre = body[:-2]
    if g != name or not args or args[1:] != list(range(1, np)):
        return False

    def defatom(d):
        for s in pre:
            if s[0] == 'a' and s[1][0] in ('const', 'add', 'mul') and s[1][1] == d:
                return s[1]
        return None

    def is_step(d):
        a = defatom(d)
        if not a or a[0] != 'mul':
            return False
        isg = lambda z: (lambda b: b is not None and b[0] == 'const' and const_ok(b[2], 1))(defatom(z))
        return (a[2] == 0 and isg(a[3])) or (a[3] == 0 and isg(a[2]))
    a = defatom(c)
    if not is_step(args[0]) or not a or a[0] != 'add':
        return False
    if endc is None:
        is_end = lambda y: np >= 2 and y == 1
    else:
        is_end = lambda y: (lambda b: b is not None and b[0] == 'const' and const_ok(b[2], endc))(defatom(y))
    return (is_step(a[2]) and is_end(a[3])) or (is_step(a[3]) and is_end(a[2]))


def end_of(body, name, np):
    """`Res.endOfFn`: `'param'` when the loop helper ends at its second parameter, else its constant end's exponent."""
    if loop_tail(body, name, np):
        return 'param'
    return next((e for e in range(256) if loop_tail(body, name, np, e)), None)


def callee_table(lk, cores, fss, bund):
    """By core name: compiled index, frame size (`B2C.fsN`), loop flag, end (`end_of`), tail (`B2C.tailN`)."""
    out = {}
    for j, (k, _, _) in lk.items():
        params, body, name = data.core_fn(cores[k])
        lp = name.startswith('__loop')
        fs = max(2, fss[k])
        out[name] = (j, fs, lp, lp and end_of(body, name, len(params)),
                     min(fs, max([len(params) + 3] + [o + 1 for o in bund[k]['env']])))
    return out


def fr_data(F, A, params, body, locs, extra, fs, cal):
    """The listed callees of a function, as `Bridge.frChk` reads them, and the offsets of the frame hints it fails.
    The callees' tails are left to the kernel."""
    loc = lambda v: extra[v] if v in extra else (locs[v] if v < len(locs) else 0)
    cell = lambda v: v not in extra and v < 1 << 30 and 2 <= loc(v) < fs
    sites = F['sites']
    frames = [(pc - A['entry'], h) for pc, l in A['hints'] for h in l if h[0] in FRAME and h[1] in sites]
    if not frames:
        return [], []
    cs, bad = set(), set()
    for st, sp, nm in stmts(body, spine(body), spine_named(body)):
        if st[0] not in ('call', 'callIf', 'dispatch'):
            continue

        def sp_const(v, e):
            return any(a[0] == 'const' and a[1] == v and const_ok(a[2], e) for a in sp)

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
        args = st[2] if st[0] == 'call' else st[3]
        rets = st[3] if st[0] == 'call' else (st[4] if st[0] == 'dispatch' else [])
        for off, h in frames:
            site = sites[h[1]]
            if list(site[0]) != list(args) or list(site[1]) != list(rets):
                continue
            ok = False
            if h[0] == 'alloc' and st[0] == 'call':
                c = cal(st[1])
                a0 = st[2][0] if st[2] else None
                ok = c is not None and ((c[1] == h[2] and not c[2]) or (
                    c[2] and isinstance(c[3], int) and not isinstance(c[3], bool) and a0 is not None and (
                        (sp_const(a0, 0) and 0 < c[3] and c[3] * c[1] + c[4] == h[2]) or
                        (sp_const(a0, 1) and 1 < c[3] and (c[3] - 1) * c[1] + c[4] == h[2]))))
                if c:
                    cs.add(c[0])
            elif h[0] == 'allocArm' and st[0] == 'dispatch':
                x, sel, sizes = st[1], h[2], h[3]
                ok = loc(x) == sel and cell(x) and (x in params or any(x in uses(a) for a in sp) or x in nm) and \
                    len(sizes) < 2 ** 28
                for i, f in enumerate(st[2]):
                    c = cal(f)
                    ok = ok and c is not None and i < len(sizes) and sizes[i] == c[1] and not c[2]
                    if c:
                        cs.add(c[0])
            elif h[0] == 'allocFrames' and st[0] == 'callIf' and len(st[3]) >= 2:
                size, stop = h[2], h[3]
                b, a0, a1 = st[1], st[3][0], st[3][1]
                c = cal(st[2])
                ok = c is not None and c[2] and c[3] == 'param' and c[1] == size and c[4] == h[5] and loc(a1) == stop \
                    and cell(a1) \
                    and ((sp_const(a0, 0) and guard(b, a1, 0)) or (sp_const(a0, 1) and guard(b, a1, 1)))
                if c:
                    cs.add(c[0])
            if not ok:
                bad.add((off, h[0]))
    return sorted(cs), sorted(bad)


def extra_of(cells):
    """A context's hint-only cells, from its literal."""
    return {int(a): int(b) for a, b in re.findall(r'\((\d+), (\d+)\)', cells)}
