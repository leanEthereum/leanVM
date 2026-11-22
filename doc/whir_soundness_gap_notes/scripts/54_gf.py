#!/usr/bin/env python3
"""54_gf.py: exact arithmetic for the referee report 54 (written for it; shares no code with the scripts of notes 35 to 53).

GF(2^16) = GF(2)[z]/(z^16 + z^12 + z^3 + z + 1), univariate polynomials as coefficient lists (low degree first),
bivariate polynomials as dicts {(i, k): coefficient of X^i Y^k}, Gaussian elimination, interpolation."""
import random

M = 16
MOD = 0x1100B
ORD = (1 << M) - 1
EXP = [0] * (2 * ORD + 2)
LOG = [0] * (1 << M)
_v = 1
for _i in range(ORD):
    EXP[_i] = _v
    LOG[_v] = _i
    _v <<= 1
    if _v >> M:
        _v ^= MOD
assert _v == 1 and len(set(EXP[:ORD])) == ORD, "modulus is not primitive"
for _i in range(ORD, 2 * ORD + 2):
    EXP[_i] = EXP[_i - ORD]


def mul(a, b):
    return EXP[LOG[a] + LOG[b]] if a and b else 0


def inv(a):
    assert a
    return EXP[ORD - LOG[a]]


def fpow(a, e):
    if e == 0:
        return 1
    if a == 0:
        return 0
    return EXP[(LOG[a] * e) % ORD]


def fsqrt(a):
    return fpow(a, 1 << (M - 1))


# ------------------------------------------------------------------ univariate polynomials

def ptrim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    if len(p) < len(q):
        p, q = q, p
    r = p[:]
    for i, c in enumerate(q):
        r[i] ^= c
    return ptrim(r)


def pmul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            la = LOG[a]
            for j, b in enumerate(q):
                if b:
                    r[i + j] ^= EXP[la + LOG[b]]
    return ptrim(r)


def pscale(p, s):
    if s == 0:
        return []
    ls = LOG[s]
    return [EXP[LOG[c] + ls] if c else 0 for c in p]


def pdeg(p):
    return len(p) - 1


def pdivmod(p, q):
    q = ptrim(q[:])
    assert q
    r = p[:]
    dq = len(q) - 1
    il = LOG[inv(q[-1])]
    out = [0] * max(len(p) - dq, 0)
    for i in range(len(r) - 1, dq - 1, -1):
        c = r[i]
        if c:
            f = EXP[LOG[c] + il]
            out[i - dq] = f
            lf = LOG[f]
            for j, b in enumerate(q):
                if b:
                    r[i - dq + j] ^= EXP[lf + LOG[b]]
    return ptrim(out), ptrim(r[:dq] if dq <= len(r) else r)


def pgcd(p, q):
    p, q = ptrim(p[:]), ptrim(q[:])
    while q:
        p, q = q, pdivmod(p, q)[1]
    if p:
        p = pscale(p, inv(p[-1]))
    return p


def pderiv(p):
    return ptrim([p[i] if i & 1 else 0 for i in range(1, len(p))])


def peval(p, x):
    r = 0
    if x == 0:
        return p[0] if p else 0
    lx = LOG[x]
    for c in reversed(p):
        r = (EXP[LOG[r] + lx] if r else 0) ^ c
    return r


def psqrt(p):
    """square root of a polynomial that is a square (all odd coefficients zero)."""
    assert all(c == 0 for c in p[1::2]), "not a square"
    return ptrim([fsqrt(c) for c in p[0::2]])


def is_square(p):
    return all(c == 0 for c in p[1::2])


def pord(p, alpha):
    """multiplicity of the root alpha of p (p != 0)."""
    assert p
    k = 0
    lin = [alpha, 1]
    while True:
        q, r = pdivmod(p, lin)
        if r:
            return k
        p = q
        k += 1


def psqfree(p):
    """squarefree part (product of the primes of odd multiplicity), monic; F perfect of characteristic 2.
    If p = O Q^2 with O squarefree then p' = O' Q^2 and gcd(p, p') = Q^2 (O is separable), so O = p / gcd(p, p')."""
    p = ptrim(p[:])
    assert p
    p = pscale(p, inv(p[-1]))
    d = pderiv(p)
    if not d:
        return [1]
    g = pgcd(p, d)
    o = pdivmod(p, g)[0]
    assert is_square(g)
    return pscale(o, inv(o[-1]))


def pinterp(xs, ys):
    """Newton interpolation; xs distinct."""
    n = len(xs)
    coef = ys[:]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = mul(coef[i] ^ coef[i - 1], inv(xs[i] ^ xs[i - j]))
    res = []
    for i in range(n - 1, -1, -1):
        # res = res * (X - xs[i]) + coef[i]
        new = [0] * (len(res) + 1)
        for k, c in enumerate(res):
            new[k + 1] ^= c
            new[k] ^= mul(c, xs[i])
        new[0] ^= coef[i]
        res = new
    return ptrim(res)


# ------------------------------------------------------------------ linear algebra

def nullspace(rows, ncols):
    """basis of {x : rows . x = 0}, rows a list of lists over GF(2^16)."""
    rows = [r[:] for r in rows if any(r)]
    piv = []
    r0 = 0
    nr = len(rows)
    for c in range(ncols):
        if r0 == nr:
            break
        p = None
        for i in range(r0, nr):
            if rows[i][c]:
                p = i
                break
        if p is None:
            continue
        rows[r0], rows[p] = rows[p], rows[r0]
        pr = rows[r0]
        liv = LOG[inv(pr[c])]
        pr = [EXP[LOG[x] + liv] if x else 0 for x in pr]
        rows[r0] = pr
        tail = [LOG[x] if x else -1 for x in pr[c:]]
        for i in range(nr):
            if i != r0:
                ri = rows[i]
                f = ri[c]
                if f:
                    lf = LOG[f]
                    rows[i] = ri[:c] + [x ^ EXP[l + lf] if l >= 0 else x for x, l in zip(ri[c:], tail)]
        piv.append(c)
        r0 += 1
    pset = set(piv)
    basis = []
    for f in range(ncols):
        if f in pset:
            continue
        x = [0] * ncols
        x[f] = 1
        for r, pc in zip(rows, piv):
            x[pc] = r[f]
        basis.append(x)
    return basis


def det(mat):
    """determinant of a square matrix over GF(2^16) (characteristic 2: no signs)."""
    n = len(mat)
    a = [r[:] for r in mat]
    d = 1
    for c in range(n):
        p = None
        for i in range(c, n):
            if a[i][c]:
                p = i
                break
        if p is None:
            return 0
        a[c], a[p] = a[p], a[c]
        pc = a[c][c]
        d = mul(d, pc)
        liv = LOG[inv(pc)]
        tail = [(LOG[x] + liv) % ORD if x else -1 for x in a[c][c:]]
        for i in range(c + 1, n):
            f = a[i][c]
            if f:
                lf = LOG[f]
                ri = a[i]
                a[i] = ri[:c] + [x ^ EXP[l + lf] if l >= 0 else x for x, l in zip(ri[c:], tail)]
    return d


# ------------------------------------------------------------------ bivariate polynomials {(i, k): c}

def binom2(a, b):
    return 1 if 0 <= b <= a and (b & ~a) == 0 else 0


def taylor(poly, alpha, beta, cap):
    """{(r, q): coefficient of T^r S^q in poly(alpha + T, beta + S)} for r + q <= cap."""
    out = {}
    for (i, k), c in poly.items():
        if not c:
            continue
        for r in range(min(i, cap) + 1):
            if not binom2(i, r):
                continue
            cr = mul(c, fpow(alpha, i - r))
            if not cr:
                continue
            for q in range(min(k, cap - r) + 1):
                if binom2(k, q):
                    v = mul(cr, fpow(beta, k - q))
                    if v:
                        out[(r, q)] = out.get((r, q), 0) ^ v
    return {k: v for k, v in out.items() if v}


def mult_at(poly, alpha, beta, cap):
    """multiplicity of poly at (alpha, beta), capped at cap + 1."""
    t = taylor(poly, alpha, beta, cap)
    return min((r + q for (r, q) in t), default=cap + 1)


def dY(poly):
    out = {}
    for (i, k), c in poly.items():
        if k & 1 and c:
            out[(i, k - 1)] = c
    return out


def dX(poly):
    out = {}
    for (i, k), c in poly.items():
        if i & 1 and c:
            out[(i - 1, k)] = c
    return out


def ycoeffs(poly):
    """list over k of the X-polynomials (coefficient lists)."""
    if not poly:
        return []
    K = max(k for (_, k) in poly)
    out = [[] for _ in range(K + 1)]
    for (i, k), c in poly.items():
        if c:
            p = out[k]
            if len(p) <= i:
                p.extend([0] * (i + 1 - len(p)))
            p[i] ^= c
    return [ptrim(p) for p in out]


def subs_poly(poly, P):
    """poly(X, P(X)) as a univariate polynomial."""
    yc = ycoeffs(poly)
    res = []
    for p in reversed(yc):
        res = padd(pmul(res, P), p)
    return res


def rand_poly(rng, deg):
    return ptrim([rng.randrange(1 << M) for _ in range(deg + 1)])


def rand_points(rng, n):
    s = set()
    while len(s) < n:
        s.add(rng.randrange(1, 1 << M))
    return sorted(s)


def subspace(rng, N):
    while True:
        basis = [rng.randrange(1, 1 << M) for _ in range(N)]
        els = [0]
        for b in basis:
            els += [e ^ b for e in els]
        if len(set(els)) == 1 << N:
            return els
