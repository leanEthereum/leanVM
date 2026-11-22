#!/usr/bin/env python3
"""Shared helpers for 40-rate-half-residual.md: GF(2^8) arithmetic, linear algebra on byte rows,
subspace domains, Taylor (Hasse) coefficients of bivariate polynomials, and the counting functions
R(m, B), N(B, Z) of note 35 (exact integers)."""
import random

M = 8
MOD = 0x11D
ORDER = (1 << M) - 1
EXP = [0] * (2 * ORDER + 2)
LOG = [0] * (1 << M)
_v = 1
for _i in range(ORDER):
    EXP[_i] = _v
    LOG[_v] = _i
    _v <<= 1
    if _v >> M:
        _v ^= MOD
for _i in range(ORDER, 2 * ORDER + 2):
    EXP[_i] = EXP[_i - ORDER]


def mul(a, b):
    if a == 0 or b == 0:
        return 0
    return EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[ORDER - LOG[a]]


def fpow(a, e):
    if e == 0:
        return 1
    if a == 0:
        return 0
    return EXP[(LOG[a] * e) % ORDER]


def fsqrt(a):
    return fpow(a, 1 << (M - 1))


TR = [bytes(mul(a, b) for b in range(1 << M)) for a in range(1 << M)]


def bxor(a, b):
    return (int.from_bytes(a, "little") ^ int.from_bytes(b, "little")).to_bytes(len(a), "little")


def rref(rows, ncols):
    """reduced row echelon form of a list of byte rows; returns (rows, pivot columns)."""
    rows = [r for r in rows if any(r)]
    piv = []
    r0 = 0
    for c in range(ncols):
        p = None
        for i in range(r0, len(rows)):
            if rows[i][c]:
                p = i
                break
        if p is None:
            continue
        rows[r0], rows[p] = rows[p], rows[r0]
        pr = rows[r0].translate(TR[inv(rows[r0][c])])
        rows[r0] = pr
        for i in range(len(rows)):
            if i != r0 and rows[i][c]:
                rows[i] = bxor(rows[i], pr.translate(TR[rows[i][c]]))
        piv.append(c)
        r0 += 1
        if r0 == len(rows):
            break
    return rows[:r0], piv


def nullspace(rows, ncols):
    """basis (list of lists) of {x : rows . x = 0}."""
    red, piv = rref(rows, ncols)
    pset = set(piv)
    free = [c for c in range(ncols) if c not in pset]
    basis = []
    for f in free:
        x = [0] * ncols
        x[f] = 1
        for r, pc in zip(red, piv):
            x[pc] = r[f]
        basis.append(x)
    return basis


def rank(rows, ncols):
    return len(rref(rows, ncols)[1])


def span(basis):
    els = [0]
    for b in basis:
        els += [e ^ b for e in els]
    return els


def subspace_domain(N, seed=1):
    """an F2-subspace of GF(2^8) of dimension N with a random basis (N <= 8)."""
    rng = random.Random(seed)
    while True:
        basis = [rng.randrange(1, 1 << M) for _ in range(N)]
        els = span(basis)
        if len(set(els)) == 1 << N:
            return els


def peval(p, x):
    r = 0
    for c in reversed(p):
        r = mul(r, x) ^ c
    return r


def binom2(a, b):
    """binomial(a, b) mod 2 (Lucas)."""
    return 1 if (b & ~a) == 0 and b <= a else 0


def taylor_row(monos, alpha, beta, r, q):
    """row of the linear form E -> coefficient of T^r S^q in E(alpha + T, beta + S), E = sum e_m X^i Y^k."""
    out = bytearray(len(monos))
    for idx, (i, k) in enumerate(monos):
        if i >= r and k >= q and binom2(i, r) and binom2(k, q):
            out[idx] = mul(fpow(alpha, i - r), fpow(beta, k - q))
    return bytes(out)


def contact_conditions(j):
    """the (r, q) with r + q < 2j, not both even: E in F[T^2, S^2] + m^(2j) iff these Taylor coefficients vanish."""
    return [(r, q) for r in range(2 * j) for q in range(2 * j - r) if (r & 1) or (q & 1)]


def support_b1(W, D):
    """monomials X^i Y^k of E, not both exponents even, with wdeg(dE) <= W for the weights (1, D, D):
    k odd: i + D k <= W (from Y1 E_Y); k even, i odd: i - 1 + D k <= W (from E_X)."""
    monos = []
    k = 0
    while D * k <= W + 1:
        for i in range(0, W + 2 - D * k):
            if (k & 1) and i + D * k <= W:
                monos.append((i, k))
            elif not (k & 1) and (i & 1) and i - 1 + D * k <= W:
                monos.append((i, k))
        k += 1
    return monos


def Rloc(m, B):
    if m <= 0 or B < 0:
        return 0
    return sum((s + 1) * (B + 1) - max(2 * s - m + 1, 0) * max(s + B - m + 1, 0) for s in range(m))


def Ncoef(B, Z, D):
    if Z <= 0 or B < 0:
        return 0
    tot, t = 0, 0
    while D * t < Z:
        tot += (min(t, B) + 1) * (Z - D * t)
        t += 1
    return tot


def lemmaC_cut(n, D, A, b, W, profile, ms):
    """exact Lemma C of note 35: profile = list of (count, contact order). Returns (m, B) if (2) holds."""
    for m in ms:
        Z = m * A
        for B in range(max(b, 1), m // 2 + 1):
            if not D * (m + B) <= Z - W:
                continue
            cost = sum(cnt * (Rloc(m, B) - Rloc(m - o, B - b)) for cnt, o in profile)
            if Ncoef(B, Z, D) - Ncoef(B - b, Z - W, D) > cost:
                return (m, B)
    return None
