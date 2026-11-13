"""Signatures and residuals for the mode walk (`LeanVM/Guest/Mode/Abs.lean`), inferred callee
first, by `walk.py`, a mirror of the Lean walk with demand hooks. Prints how many functions pass,
and the residuals and failures. Not yet a certificate generator."""
import sys, os, collections
sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from walk import *
import data
P = data.load()
fns, HINTS, POWS, JT = P['fns'], P['hints'], P['pows'], P['jt']
byentry = {f['entry']: f for f in fns.values()}
JT_LO, JT_HI, HALT = 430, 14367, 2 ** 19 - 1


def conv(op, a):
    if op in ('xor', 'mul'): return tuple(map(int, a))
    if op == 'set': return tuple(map(int, a))
    if op == 'deref': return (int(a[0]), int(a[1]), int(a[2]), a[3])
    if op == 'jump': return tuple(map(int, a))
    if op == 'keccak': return tuple(map(int, a[:8])) + (a[8] == 'true', a[9] == 'true', a[10])
    raise Exception(op)


for f in fns.values():
    f['ops'] = [(op, conv(op, a)) for op, a in f['code']]
    f['hints'] = {pc - f['entry']: hs for pc, hs in HINTS.items() if f['entry'] <= pc < f['entry'] + f['count']}

_b = set()
for f in fns.values():
    c = f['ops']
    for i in range(1, len(c)):
        a, b = c[i - 1], c[i]
        if a[0] == 'deref' and b[0] == 'jump' and a[1][3] == '.cell' and a[1][2] == b[1][1]:
            _b.add(a[1][1])
_bl = sorted(_b)
REGION = {t: (_bl[k + 1] if k + 1 < len(_bl) else JT_HI) - t for k, t in enumerate(_bl)}
for f in fns.values():
    c = f['ops']; f['tabs'] = {}
    for i in range(1, len(c)):
        a, b = c[i - 1], c[i]
        if a[0] == 'deref' and b[0] == 'jump' and a[1][3] == '.cell' and a[1][2] == b[1][1]:
            f['tabs'][i] = REGION[a[1][1]]

E = Env(POWS, JT, JT_LO, JT_HI, HALT)

calls = collections.defaultdict(set)
for f in fns.values():
    for op, a in f['ops']:
        if op == 'set' and a[2] == 0 and POWS.get(a[1]) in byentry:
            calls[f['name']].add(byentry[POWS[a[1]]]['name'])
    c = f['ops']
    for i in range(1, len(c)):
        a, b = c[i - 1], c[i]
        if a[0] == 'deref' and b[0] == 'jump' and a[1][3] == '.cell' and a[1][2] == b[1][1]:
            for j in range(REGION[a[1][1]]):
                g = byentry.get(JT.get(a[1][1] + j))
                if g: calls[f['name']].add(g['name'])
order = []; seen = set()


def dfs(n):
    seen.add(n)
    for m in sorted(calls[n]):
        if m not in seen and m != n: dfs(m)
    order.append(n)


for n in sorted(fns, key=lambda n: fns[n]['entry']):
    if n not in seen: dfs(n)

# loop helpers: a tail call into themselves; their self cell
isloop = set()
selfc = {}
for f in fns.values():
    c = f['ops']
    for i, (op, a) in enumerate(c):
        if op == 'deref' and a[3] == '.cell' and a[0] == a[2]:
            for d in range(1, 5):
                if i + d < len(c) and c[i + d][0] == 'jump':
                    od = c[i + d][1][1]
                    for k in range(i - 1, max(-1, i - 300), -1):
                        if c[k][0] == 'set' and c[k][1][0] == od:
                            e = POWS.get(c[k][1][1])
                            if e is not None: selfc[e] = a[1]
                            break
                    break
for f in fns.values():
    if f['name'] in calls[f['name']]: isloop.add(f['name'])


def params(f): return set(range(2, 2 + f.get('nargs', 0)))


def ifaceBase(f, b):
    return b[1] in params(f)


def ifaceMono(f, m):
    return m[0] == 0 and all(ifaceBase(f, b) for b, e in m[2])


def ifaceIdx(f, i):
    return i[0] == 'num' or ifaceBase(f, i[1])


class Infer:
    def __init__(self, f):
        self.f = f; self.pre = set(); self.preR = set(); self.res = collections.defaultdict(list)
        self.new = False; self.unres = []

    def demand(self, kind, i, *rest):
        f = self.f
        if kind == 'lnk':
            o, (k, i0), A = rest
            return self.key(k, i0, A)
        if kind == 'nz':
            kn, A = rest
            self.res[i].append(('nz', kn)); self.new = True; return True
        if kind == 'pre':
            name, m, k, A = rest
            if isinstance(name, tuple) and name[0] == 'tail':
                return False
            if k is not None: return self.key(k, i, A)
            return False
        if kind == 'preR':
            name, r, r2, A = rest
            if isinstance(name, tuple) and name[0] == 'tail': return False
            if r2 is not None and ifaceMono(f, r2[0]) and ifaceIdx(f, r2[1]) and ifaceIdx(f, r2[2]) and r2[0][2]:
                self.preR.add(r2); self.new = True; A.r.add(r2); return True
            return False
        if kind == 'entry':
            name, o, A, cs, lnk = rest
            for c in cs:
                if c in lnk and lnk[c][0] != None:
                    k2, i0 = lnk[c]
                    if self.key(k2, i0, A):
                        return True
            return False
        if kind == 'H':
            k, A = rest
            return self.key(k, i, A)
        if kind == 'sel':
            x, n, A = rest
            r = ('lt', ('ex', x, 0), ('num', n))
            self.res[i].append(r); self.new = True; A.lt.add((r[1], r[2])); return True
        return False

    def key(self, k, i0, A):
        f = self.f
        if k[0] == 0 and k[2] and ifaceMono(f, k):
            self.pre.add(k); self.new = True; A.h.add(k); return True
        if k[0] != 0 or not k[2]: return False
        for (x, e) in k[2]:
            if x[0] != 'fr': continue
            Q = tuple((b, ee) for b, ee in k[2] if b != x)
            if not (Q and ifaceMono(f, (0, 0, Q))): continue
            for (p, hi) in sorted(A.lt, key=lambda t: (t[1][0] != 'num', t[1][1] if t[1][0] == 'num' else 0)):
                if p == ('ex', x, 0) and ifaceIdx(f, hi) and hi != ('num', MAXCELLS):
                    r = ((0, 0, Q), ('num', 0), hi, e, k[1])
                    self.preR.add(r); self.new = True; A.r.add(r); return True
        # a jump table load through an unbounded selector: residual bound
        if k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1 and k[1] in REGION:
            x = k[2][0][0]
            r = ('lt', ('ex', x, 0), ('num', REGION[k[1]]))
            if r not in self.res[i0]:
                self.res[i0].append(r); self.new = True
            A.lt.add((r[1], r[2])); return True
        return False


def mkSig(f, pre, preR, ret=(), post=(), postR=(), postL=()):
    loop = f['name'] in isloop
    term = [(('ex', ('fr', 2), 0), ('ex', ('fr', 3), 0))] if loop else []
    return Sig(f['entry'], list(range(2 + f.get('nargs', 0))), selfc.get(f['entry']), sorted(pre), sorted(preR), term,
               ret, sorted(post), sorted(postR), sorted(postL))


def renameRet(f, A, m):
    """A product over the walk's bases in the function's own terms (parameters, return cells)."""
    rets = range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f.get('nret', 0))
    ren = {}
    for r in rets:
        x = A.v.get(r)
        if x and x[0] == 'm' and x[1][0] == 0 and x[1][1] == 0 and len(x[1][2]) == 1 and x[1][2][0][1] == 1:
            ren.setdefault(x[1][2][0][0], ('fr', r))
    bs = tuple(sorted((ren.get(b, b), e) for b, e in m[2]))
    return (m[0], m[1], bs)


def okIface(f, m):
    rets = set(range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f.get('nret', 0)))
    return m[0] == 0 and m[2] and all(b[1] in params(f) or (b[0] == 'fr' and b[1] in rets) for b, e in m[2])


def infer(n):
    f = fns[n]
    I = Infer(f)
    main = n == 'main'
    for it in range(40):
        sig = mkSig(f, I.pre, I.preR)
        E.sigs[f['entry']] = sig
        I.new = False
        w = Walk(E, f['entry'], f['count'], sig, f['hints'], I.res, f['tabs'], main=main, demand=I.demand)
        try:
            w.run(f['ops'])
        except Fail as e:
            if not I.new:
                # loop transport: generalize uncovered pre points over the counter
                if n in isloop and e.args[0][0] == 'pre' and isinstance(e.args[0][2], tuple):
                    m = e.args[0][3]
                    S = dict(m[2]).get(('fr', 2))
                    if S:
                        Q = tuple((b, x) for b, x in m[2] if b != ('fr', 2))
                        I.pre.discard(m)
                        I.preR.add(((0, 0, Q), ('ex', ('fr', 2), 0), ('ex', ('fr', 3), 0), S, m[1]))
                        continue
                raise
            continue
        if not I.new: break
    else:
        raise Fail(('nofix',))
    # posts
    nr = f.get('nret', 0); na = f.get('nargs', 0)
    rets = list(range(2 + na, 2 + na + nr))
    ret = [o for o in rets if all(o in A.w for A in w.rets)] if w.rets else rets
    post = None; postR = None
    for A in w.rets:
        ks = {renameRet(f, A, k) for k in A.h}
        ks = {k for k in ks if okIface(f, k)}
        post = ks if post is None else post & ks
        rs = set()
        for (q, lo, hi, S, d) in A.r:
            q2 = renameRet(f, A, q)
            if okIface(f, q2) and ifaceIdx(f, lo) and ifaceIdx(f, hi): rs.add((q2, lo, hi, S, d))
        postR = rs if postR is None else postR & rs
    post = post or set(); postR = postR or set()
    postL = set()
    if n in isloop:
        ends = w.rets + [t[0] for t in w.tails]
        cand = None
        for A in ends:
            ks = {k for k in A.h if k[0] == 0 and dict(k[2]).get(('fr', 2)) and ifaceMono(f, k)}
            cand = ks if cand is None else cand & ks
        for k in cand or ():
            S = dict(k[2])[('fr', 2)]
            Q = tuple((b, x) for b, x in k[2] if b != ('fr', 2))
            if Q: postL.add(((0, 0, Q), ('ex', ('fr', 2), 0), ('ex', ('fr', 3), 0), S, k[1]))
        post = set(); postR = set()
    sig = mkSig(f, I.pre, I.preR, ret, post, postR, postL)
    E.sigs[f['entry']] = sig
    # the final check: no demand
    w = Walk(E, f['entry'], f['count'], sig, f['hints'], I.res, f['tabs'], main=main)
    try:
        w.run(f['ops'])
    except Fail as e:
        # drop what does not check
        sig = mkSig(f, I.pre, I.preR, ret, set(), set(), set())
        E.sigs[f['entry']] = sig
        w = Walk(E, f['entry'], f['count'], sig, f['hints'], I.res, f['tabs'], main=main)
        w.run(f['ops'])
    return sig, dict(I.res)


if __name__ == '__main__':
    sigs = {}; fails = {}; res = {}
    for n in order:
        f = fns[n]
        try:
            sigs[n], res[n] = infer(n)
        except Fail as e:
            fails[n] = e.args[0]
            sig = mkSig(f, [], [], list(range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f.get('nret', 0))))
            E.sigs[f['entry']] = sig; sigs[n] = sig
    print('fail', len(fails), collections.Counter(v[0] for v in fails.values()).most_common())
    rk = collections.Counter(r[0] for n in res for rs in res[n].values() for r in rs)
    print('resid kinds', rk, 'fns with resid', sum(1 for n in res if any(res[n].values())))
    print('clean', sum(1 for n in sigs if n not in fails and not any(res.get(n, {}).values())))
    rootf = [n for n in fails if not any(m in fails for m in calls[n] if m != n)]
    print('root failures', len(rootf), collections.Counter(fails[n][0] for n in rootf))
    for n in sorted(rootf, key=lambda n: fns[n]['count'])[:40]:
        e = fails[n]
        print(n, fns[n]['count'], str(e[:4] if isinstance(e, tuple) else e)[:200])
