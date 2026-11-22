#!/usr/bin/env python3
"""Toy-field checks for note 03 (attack model and knobs). Pure python, GF(2^8), about a minute.

E = GF(2^8) = F_2[x]/(x^8+x^4+x^3+x+1), D = span(1, x, ..., x^(N-1)) = the integers below 2^N.
Every count below is exhaustive over all |E|^2 = 65536 fold challenges (alpha, beta).

 1. flats (lead notes, section 1), on n = 16, rate 1/4.
 2. a fold round against a list: the escape set is a union of conics, about L |E| pairs;
    with a shared F half it is a union of L lines; with two independent claims it is O(L) points,
    unless the message is tailored to one candidate (then a whole line again).
 3. the coset pole pair with NONZERO weights: n/|W| whole lines escape when the claim is the
    pseudo-pair's; at most 2 per line for a generic message; one whole line for a tailored message.
 4. the coset-union family with one more coefficient pinned by pigeonhole (slack-1 lists).
"""
import itertools, random

random.seed(3)
Q = 256
EXP, LOG = [0] * 510, [0] * 256
# 3 = x + 1 generates the multiplicative group (x does not, for 0x11B)
v = 1
for i in range(255):
    EXP[i], LOG[v] = v, i
    w = v << 1
    if w & 0x100:
        w ^= 0x11B
    v = w ^ v
for i in range(255, 510):
    EXP[i] = EXP[i - 255]


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]


def inv(a):
    assert a
    return EXP[255 - LOG[a]]


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) ^ (q[i] if i < len(q) else 0) for i in range(n)]


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] ^= mul(a, b)
    return r


def pscale(s, p):
    return [mul(s, a) for a in p]


def peval(p, x):
    r = 0
    for a in reversed(p):
        r = mul(r, x) ^ a
    return r


def deg(p):
    d = len(p) - 1
    while d >= 0 and p[d] == 0:
        d -= 1
    return d


def span(basis):
    s = [0]
    for b in basis:
        s += [u ^ b for u in s]
    return s


def locator(points):
    p = [1]
    for u in points:
        p = pmul(p, [u, 1])
    return p


def lin(L, p):
    """The linear functional with coefficient vector L on the coefficient vector of p."""
    r = 0
    for a, b in zip(L, p):
        r ^= mul(a, b)
    return r


def rnd(k):
    return [random.randrange(1, Q) for _ in range(k)]


def template(m, c, a, b):
    """The verifier's folded claim: u0 + a (c + u0) + a^2 v + b c0 + a b (c0 + c1)."""
    u0, vF, c0, c1 = m
    return u0 ^ mul(a, c ^ u0) ^ mul(mul(a, a), vF) ^ mul(b, c0) ^ mul(mul(a, b), c0 ^ c1)


def folded_claim_of(L0, L1, P, a):
    """(1 + a) L0(P) + a L1(P): the folded weight against P."""
    return mul(1 ^ a, lin(L0, P)) ^ mul(a, lin(L1, P))


def honest(L0, L1, F, G):
    XF = [0] + F
    return (lin(L0, G), lin(L0, F) ^ lin(L1, F), lin(L0, XF), lin(L1, XF)), lin(L0, F) ^ lin(L1, G)


# ---------------------------------------------------------------- 1. flats
print("== 1. flats, n = 16, kappa = 2, rate 1/4")
N, kappa = 4, 2
D = list(range(1 << N))
hyper = []
for phi in range(1, 1 << N):  # hyperplanes = kernels of nonzero functionals on F_2^N
    V = [u for u in D if bin(u & phi).count("1") % 2 == 0]
    hyper.append(V)
wflat = [EXP[(LOG[x] * 7) % 255] if x else 0 for x in D]  # x^(2^(kappa+1) - 1)
flats = []
for V in hyper:
    LV = locator(V)
    assert LV[0] == 0 and LV[8] == 1
    QV = LV[1:8]  # (L_V - X^8) / X
    assert deg(QV) == (1 << kappa) - 1
    agree = sum(peval(QV, x) == wflat[x] for x in D)
    assert agree == 7, agree
    flats.append(QV[:4])
assert len({tuple(q) for q in flats}) == 15
print("   15 hyperplanes, 15 distinct Q_V of degree 3 = 2^kappa - 1, each agreeing with x^7 on exactly 7 = n/2 - 1 points")

# ---------------------------------------------------------------- 2. a fold round against a list
print("== 2. fold round against the flats list (L = 15), |E| = 256")
dmax = 6  # coefficient vectors of length 6 hold degrees up to 5 (d + 1 with d = 4)
L0, L1 = rnd(dmax), rnd(dmax)


def escapes(cands, m, c, weights=(None, None)):
    """Challenges after which some candidate's fold satisfies the folded claim (all coordinates)."""
    hit = set()
    per = []
    for (F, G) in cands:
        XF = [0] + F
        cnt = 0
        for a in range(Q):
            GaF = padd(G, pscale(a, F))
            for b in range(Q):
                P = padd(GaF, pscale(b, XF))
                ok = True
                for (W0, W1), mm, cc in weights:
                    if folded_claim_of(W0, W1, P, a) != template(mm, cc, a, b):
                        ok = False
                        break
                if ok:
                    cnt += 1
                    hit.add((a, b))
        per.append(cnt)
    return hit, per


# 2a: generic list, both halves vary: pairs (Q_V, s Q_V), common agreement V \ {0}
s = 0x37
cands = [(q, pscale(s, q)) for q in flats]
c = 0x5A
assert all(honest(L0, L1, F, G)[1] != c for F, G in cands)
m = tuple(rnd(4))
hit, per = escapes(cands, m, c, weights=[((L0, L1), m, c)])
print(f"   2a generic message: per-candidate zeros min/max = {min(per)}/{max(per)}, union = {len(hit)} = {len(hit)/Q:.2f} |E|  (L = 15)")

# 2b: shared F half (the list varies in the G half only); the message is honest for F
F = [3, 1, 4, 1]
cands_b = [(F, q) for q in flats]
mF, _ = honest(L0, L1, F, flats[0])
mb = (0x21, mF[1], mF[2], mF[3])  # u0 free, v, c0, c1 true for the shared F
assert all(honest(L0, L1, F, G)[1] != c for F, G in cands_b)
hit, per = escapes(cands_b, mb, c, weights=[((L0, L1), mb, c)])
alphas = {a for a, _ in hit}
print(f"   2b shared F: union = {len(hit)} = {len(alphas)} whole lines alpha = const (each candidate: {sorted(set(per))} zeros)")
assert len(hit) == len(alphas) * Q

# 2c: two independent claims (second weight pair, second claim, second table)
M0, M1 = rnd(dmax), rnd(dmax)
c2 = 0xC3
m2 = tuple(rnd(4))
hit, per = escapes(cands, m, c, weights=[((L0, L1), m, c), ((M0, M1), m2, c2)])
print(f"   2c two claims, generic tables: union = {len(hit)} points (bound 4 L = 60), per candidate max {max(per)}")
# tailored to candidate 0 on the line alpha = a0: the candidate's honest tables except u0, shifted so that
# both residuals are e (alpha + a0) / (1 + a0) ... solved directly: residual = dG (1 + alpha) + alpha e
a0 = 0x9D
Fc, Gc = cands[0]
tabs = []
for (W0, W1), cc in (((L0, L1), c), ((M0, M1), c2)):
    (u0, vF, c0, c1), ctrue = honest(W0, W1, Fc, Gc)
    e = ctrue ^ cc
    dG = mul(mul(a0, e), inv(1 ^ a0))  # dG (1 + a0) = a0 e
    tabs.append(((W0, W1), (u0 ^ dG, vF, c0, c1), cc))
hit, per = escapes(cands, None, None, weights=tabs)
print(f"   2c two claims, tables tailored to one candidate: union = {len(hit)} (its line alpha = a0: {per[0]} zeros; the others: max {max(per[1:])})")
assert per[0] == Q

# ---------------------------------------------------------------- 3. coset pole pair, nonzero weights
print("== 3. coset pole pair, n = 32, |W| = 8 (4 cosets), d = 1, threshold a = 8")
N = 5
D = list(range(1 << N))
Wsub = list(range(8))
LW = locator(Wsub)
beta0 = 0x53
assert beta0 not in D
f0 = [inv(x ^ beta0) for x in D]
f1 = [mul(peval(LW, x), f0[x]) for x in D]
labels = sorted({peval(LW, x) for x in D})
assert len(labels) == 4
MULX = [[mul(sl, x) for x in D] for sl in range(Q)]
INVD = [0] + [inv(u) for u in range(1, 32)]


def lines_through(word, pairs, need):
    found = set()
    for i, j in pairs:
        sl = mul(word[i] ^ word[j], INVD[i ^ j])
        t = word[i] ^ MULX[sl][i]
        row = MULX[sl]
        agree = 0
        for k in range(32):
            if word[k] == t ^ row[k]:
                agree += 1
        if agree >= need:
            found.add((t, sl))
    return found


allpairs = list(itertools.combinations(range(32), 2))
best = max(max(sum(w[k] == (w[i] ^ MULX[mul(w[i] ^ w[j], INVD[i ^ j])][i]) ^ MULX[mul(w[i] ^ w[j], INVD[i ^ j])][k] for k in range(32)) for i, j in allpairs) for w in (f0,))
print(f"   3a f0 = 1/(x - beta0) agrees with every line on at most {best} points: no pair within a - 1 = 7, every claim is 'violated'")
# a line agreeing on 8 of 32 points has two of them in one of 7 blocks
blocks = [list(range(0, 5)), list(range(5, 10)), list(range(10, 15)), list(range(15, 20)), list(range(20, 24)), list(range(24, 28)), list(range(28, 32))]
cover = [p for blk in blocks for p in itertools.combinations(blk, 2)]
close = {}
for a in range(Q):
    for b in range(Q):
        row = MULX[b]
        word = [f1[k] ^ mul(a ^ row[k], f0[k]) for k in range(32)]
        got = lines_through(word, cover, 8)
        if got:
            close[(a, b)] = got
on_lines = {(a, b) for a in range(Q) for b in range(Q) if (a ^ mul(b, beta0)) in labels}
print(f"   3b challenges whose fold is 8-close to a line: {len(close)}; those with alpha + beta beta0 a coset label: {len(on_lines)} = 4 |E|; all of them close: {on_lines <= set(close)}")
assert all((b, 0) in close[t] for t in on_lines for b in [t[1]])  # P = the constant beta
K0, K1 = rnd(2), rnd(2)  # nonzero weights on (p0, p1)


def pole_escapes(m, c):
    n_all = n_line = 0
    for (a, b), polys in close.items():
        if any(folded_claim_of(K0, K1, list(P), a) == template(m, c, a, b) for P in polys):
            n_all += 1
            n_line += (a, b) in on_lines
    return n_all, n_line


one = [1, 0]
m1 = (0, 0, lin(K0, one), lin(K1, one))
print(f"   3c claim c = 0, table (0, 0, L0(1), L1(1)), weights nonzero: escapes = {pole_escapes(m1, 0)[0]} (= 4 |E|: every bad line, whole)")
print(f"      same table, c = 0x11: escapes = {pole_escapes(m1, 0x11)[0]}")
worst = max(pole_escapes(tuple(rnd(4)), random.randrange(1, Q))[0] for _ in range(20))
print(f"      20 random tables and claims: max escapes = {worst} (2 per line would be 8)")
# tailored to the line gamma: three linear equations in (u0, v, c0, c1); take c0 free
g = labels[1]
cc = 0x77
ib = inv(beta0)
l0, l1 = lin(K0, one), lin(K1, one)
c0 = 0x42
u0 = mul(mul(g, ib), l0 ^ c0)
# alpha coefficient: c + u0 + c0/b0 + g (c0 + c1)/b0 = l0/b0 + g (l0 + l1)/b0
rhs = mul(l0, ib) ^ mul(mul(g, ib), l0 ^ l1) ^ cc ^ u0 ^ mul(c0, ib)
s01 = mul(rhs, inv(mul(g, ib)))  # c0 + c1
c1 = c0 ^ s01
vv = mul(ib, l0 ^ l1 ^ s01)
print(f"      c = 0x77, table tailored to one line: escapes (all, on bad lines) = {pole_escapes((u0, vv, c0, c1), cc)}  (one whole line = 256)")

# ---------------------------------------------------------------- 4. pigeonhole coset-union family
print("== 4. coset unions with e_1 pinned: n = 64, rate 1/2 (kappa = 5), M = 8 cosets, m = 6")
N = 6
D = list(range(1 << N))
LW = locator(list(range(8)))
labels = sorted({peval(LW, x) for x in D})
assert len(labels) == 8
classes = {}
for U in itertools.combinations(labels, 6):
    e1 = 0
    for u in U:
        e1 ^= u
    classes.setdefault(e1, []).append(U)
sizes = sorted(len(v) for v in classes.values())
e1, fam = max(classes.items(), key=lambda kv: len(kv[1]))
LWp = [[1]]
for _ in range(6):
    LWp.append(pmul(LWp[-1], LW))
word = padd(LWp[6], pscale(e1, LWp[5]))
ok = True
polys = set()
for U in fam:
    VU = [1]
    for u in U:
        VU = pmul(VU, [u, 1])
    comp = [0]
    for k, a in enumerate(VU):
        comp = padd(comp, pscale(a, LWp[k]))
    CU = padd(comp, word)
    agree = sum(peval(CU, x) == peval(word, x) for x in D)
    ok &= deg(CU) <= 32 and agree >= 48
    polys.add(tuple(CU))
print(f"   e_1 classes of the C(8,6) = 28 subsets: {sizes}; one class: {len(polys)} distinct polynomials of degree <= 2^kappa = 32 agreeing with one word on 48 = 3n/4 points: {ok}")
