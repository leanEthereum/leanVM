#!/usr/bin/env python3
"""50_lattice.py: first integrals of Y1-degree <= b with prescribed contact along the lines of a word, by linear algebra
over GF(2^8).  For 50-residual-b-at-least-2.md, Sections 2, 3 and 6.

Normal form (note 43 Section 6.2, note 45 Section 5): G = sum_c v^c G0c(tau, q) + u sum_c v^c G1c(tau, q), q = u^2 + tau v^2,
with c <= b in the first sum and c <= b - 1 in the second.  In jet coordinates tau = X^2, q = Y0^2, u = Y0 + X Y1, v = Y1.
Weighted degree (weights (1, D, D)) of tau^i q^k v^c: 2i + (2k + c) D; of tau^i q^k u v^c: 2i + 1 + (2k + c + 1) D; the leading
monomials are distinct, so the weighted degree of a combination is the maximum.
Contact >= 2j on the line of (alpha, y): in the local coordinates t1 = tau - alpha^2, t2 = u + alpha v - y one has
tau = alpha^2 + t1, u = y + alpha v + t2, q = y^2 + t2^2 + t1 v^2, and the condition is that no monomial t1^c t2^d v^e with
c + d < j occurs.

The script processes the basis in the order of the weighted degree with an incremental elimination, so that it gets at once,
for every W, a basis of the solutions of weighted degree <= W.  It prints
  * the rank of the conditions per line (against the count of 50_local.py, Corollary 2.4);
  * the successive minima and the conservation law  sum W_i = sum w_i + 2 * (number of conditions);
  * W_II(b): the smallest W at which a solution with Y1-degree exactly b and leading coefficient involving Y0 exists,
    against the bound (L1) of Theorem 3.1:  (b + d) D + sum_alpha max(j_alpha - d/2, 2 j_alpha - b - d, 0), d = deg_Y0 G_b;
  * on every basis solution found: Lemma 2.1 and Corollary 2.3 (supports of the Taylor expansions of the Y1-coefficients
    at every received point), the fibre statement and the content of the leading coefficient (Theorem 3.1);
  * W_irr: the smallest W at which a random solution (Y1-degree b, case II) is absolutely irreducible over F(tau)
    (test: a specialization tau = tau0 of full degree whose restrictions to random lines have factorization patterns that
    exclude every splitting, and which has a nonsingular GF(2^8)-point).

Run: python3 50_lattice.py N b j [key=value ...]
   N: n = 2^N points;  b: Y1-degree bound;  j: contact 2j is imposed
   word=rand|fam|zero|mono:<e>|plant:<errors>|two        (default rand)     plant: a codeword of degree <= D with <errors> errors
   dom=sub|pts                                           (default sub)      F2-subspace or n arbitrary points of GF(2^8)
   x=<float>     contact 2j on the first round(x n) lines, contact 2*jrest on the others (default x = 1)
   jrest=0|1     (default 0)
   D=<int>       degree bound (default n/2 - 1)
   wmax=<float>  largest W / n explored (default: enough for all minima up to the mean + margin)
   seed=<int>    irr=0|1 (default 1)
"""
import sys
import random
from importlib import import_module

lib = import_module("40_lib")
mul, fpow, inv = lib.mul, lib.fpow, lib.inv
TR = lib.TR


def binom2(a, b):
    return 1 if 0 <= b <= a and (b & ~a) == 0 else 0


# ------------------------------------------------------------------ truncated polynomials in (t1, t2, v)
def tmul(a, b, j):
    out = {}
    for (c1, d1, e1), x1 in a.items():
        for (c2, d2, e2), x2 in b.items():
            if c1 + c2 + d1 + d2 < j:
                key = (c1 + c2, d1 + d2, e1 + e2)
                val = out.get(key, 0) ^ mul(x1, x2)
                if val:
                    out[key] = val
                else:
                    out.pop(key, None)
    return out


def local_expansions(al, y, j, basis):
    """for every basis element (typ, i, k, c0) its expansion truncated at c + d < j, as a dict (c, d, e) -> value."""
    a2, y2 = mul(al, al), mul(y, y)
    imax = max(i for (_, i, _, _) in basis)
    kmax = max(k for (_, _, k, _) in basis)
    taup = []
    for i in range(imax + 1):
        d = {}
        for c in range(0, min(i, j - 1) + 1):
            if binom2(i, c):
                val = fpow(a2, i - c)
                if val:
                    d[(c, 0, 0)] = val
        taup.append(d)
    qb = {}
    if y2:
        qb[(0, 0, 0)] = y2
    if j > 2:
        qb[(0, 2, 0)] = 1
    if j > 1:
        qb[(1, 0, 2)] = 1
    qp = [{(0, 0, 0): 1}]
    for k in range(1, kmax + 1):
        qp.append(tmul(qp[-1], qb, j))
    ub = {}
    if y:
        ub[(0, 0, 0)] = y
    if al:
        ub[(0, 0, 1)] = al
    if j > 1:
        ub[(0, 1, 0)] = 1
    quk = [tmul(qp[k], ub, j) for k in range(kmax + 1)]
    out = []
    for (typ, i, k, c0) in basis:
        base = qp[k] if typ == 0 else quk[k]
        e = tmul(taup[i], base, j)
        out.append({(c, d, ee + c0): val for (c, d, ee), val in e.items()})
    return out


def make_basis(b, Dc, Wmax):
    """(weight, typ, i, k, c0): typ 0 = tau^i q^k v^c0 (c0 <= b), typ 1 = tau^i q^k u v^c0 (c0 <= b - 1)."""
    out = []
    for c0 in range(b + 1):
        k = 0
        while (2 * k + c0) * Dc <= Wmax:
            i = 0
            while 2 * i + (2 * k + c0) * Dc <= Wmax:
                out.append((2 * i + (2 * k + c0) * Dc, 0, i, k, c0))
                i += 1
            k += 1
    for c0 in range(b):
        k = 0
        while 1 + (2 * k + c0 + 1) * Dc <= Wmax:
            i = 0
            while 2 * i + 1 + (2 * k + c0 + 1) * Dc <= Wmax:
                out.append((2 * i + 1 + (2 * k + c0 + 1) * Dc, 1, i, k, c0))
                i += 1
            k += 1
    out.sort()
    return out


def bxor(a, b):
    return (int.from_bytes(a, "little") ^ int.from_bytes(b, "little")).to_bytes(len(a), "little")


def solve(pts, prof, b, Dc, Wmax):
    """pts: list of (alpha, y); prof: list of j (same length).  Returns (basis, kernel) where kernel is a list of
    (weight, coefficient list over basis) in the order of the weight, a basis of the solutions of weight <= Wmax."""
    wb = make_basis(b, Dc, Wmax)
    basis = [(t, i, k, c0) for (_, t, i, k, c0) in wb]
    M = len(basis)
    # condition rows
    cols = [dict() for _ in range(M)]        # column index -> {row key: value}
    keyindex = {}
    for pi, ((al, y), j) in enumerate(zip(pts, prof)):
        if j == 0:
            continue
        ex = local_expansions(al, y, j, basis)
        for m, e in enumerate(ex):
            for key, val in e.items():
                rk = (pi,) + key
                if rk not in keyindex:
                    keyindex[rk] = len(keyindex)
                cols[m][keyindex[rk]] = val
    Rn = len(keyindex)
    pivots = []          # (position, vector bytes of length Rn + M)
    kernel = []
    rank_per_point = None
    for m in range(M):
        vec = bytearray(Rn + M)
        for r, val in cols[m].items():
            vec[r] = val
        vec[Rn + m] = 1
        x = bytes(vec)
        for pos, pv in pivots:
            cf = x[pos]
            if cf:
                x = bxor(x, pv.translate(TR[cf]))
        head = x[:Rn]
        if any(head):
            pos = next(i for i, val in enumerate(head) if val)
            x = x.translate(TR[inv(x[pos])])
            pivots.append((pos, x))
        else:
            kernel.append((wb[m][0], list(x[Rn:])))
    return wb, kernel, len(pivots)


# ------------------------------------------------------------------ polynomials in (X, Y0, Y1) as dicts
def to_jet(wb, coeffs):
    """the jet form: dict (x, a, e) -> value for the monomial X^x Y0^a Y1^e."""
    G = {}
    for (w, typ, i, k, c0), cf in zip(wb, coeffs):
        if not cf:
            continue
        if typ == 0:
            key = (2 * i, 2 * k, c0)
            G[key] = G.get(key, 0) ^ cf
        else:
            for key in ((2 * i, 2 * k + 1, c0), (2 * i + 1, 2 * k, c0 + 1)):
                G[key] = G.get(key, 0) ^ cf
    return {key: v for key, v in G.items() if v}


def wdeg(G, Dc):
    return max(x + Dc * (a + e) for (x, a, e) in G)


def taylor2(P, al, y):
    """P: dict (x, a) -> value; returns dict (r, q) -> coefficient of T^r S^q in P(al + T, y + S)."""
    out = {}
    for (x, a), val in P.items():
        for r in range(x + 1):
            if not binom2(x, r):
                continue
            ax = fpow(al, x - r)
            if not ax:
                continue
            for q in range(a + 1):
                if not binom2(a, q):
                    continue
                ya = fpow(y, a - q)
                if not ya:
                    continue
                key = (r, q)
                out[key] = out.get(key, 0) ^ mul(val, mul(ax, ya))
    return {key: v for key, v in out.items() if v}


ORD_OFFSET = {1: [-1, -1], 2: [-2, -1, -2], 3: [-3, -3, -3, -3], 4: [-4, -3, -3, -3, -4], 5: [-5, -5, -3, -3, -5, -5]}


def check_solution(G, pts, prof, Dc):
    """returns (b, d_b, W, list of failed checks)."""
    b = max(e for (_, _, e) in G)
    coef = [dict() for _ in range(b + 1)]
    for (x, a, e), val in G.items():
        coef[e][(x, a)] = val
    db = max(a for (x, a) in coef[b])
    W = wdeg(G, Dc)
    fails = []
    lead = coef[b]
    for (al, y), j in zip(pts, prof):
        if j == 0:
            continue
        m = 2 * j
        for c in range(b + 1):
            if not coef[c]:
                continue
            ty = taylor2(coef[c], al, y)
            for (r, q) in ty:
                if not (r + q >= max(j, m - b) and 2 * r + q >= m - (b - c) and r + 2 * q >= m - c):
                    fails.append(("N'", al, c, r, q))
                if j >= b and b in ORD_OFFSET and r + q < m + ORD_OFFSET[b][c]:
                    fails.append(("ord", al, c, r, q))
            if c == b:
                eps = max(j - db // 2, 2 * j - b - db, 0)
                if any(r < eps for (r, q) in ty):
                    fails.append(("content", al, eps))
                if any(r == 0 and q < m for (r, q) in ty):
                    fails.append(("fibre", al))
    l1 = (b + db) * Dc + sum(max(j - db // 2, 2 * j - b - db, 0) for j in prof)
    if db >= 2 and W < l1:
        fails.append(("L1", W, l1))
    return b, db, W, fails


# ------------------------------------------------------------------ absolute irreducibility (probabilistic certificate)
def pmod(a, f):
    a = a[:]
    df = len(f) - 1
    iv = inv(f[-1])
    while len(a) - 1 >= df and any(a):
        if a[-1]:
            cf = mul(a[-1], iv)
            sh = len(a) - 1 - df
            for i, c in enumerate(f):
                if c:
                    a[sh + i] ^= mul(cf, c)
        a.pop()
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def pmulmod(a, bb, f):
    out = [0] * (len(a) + len(bb) - 1)
    for i, x in enumerate(a):
        if x:
            for k, z in enumerate(bb):
                if z:
                    out[i + k] ^= mul(x, z)
    return pmod(out, f)


def pgcd(a, bb):
    a, bb = a[:], bb[:]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    while len(bb) > 1 and bb[-1] == 0:
        bb.pop()
    while any(bb):
        a, bb = bb, pmod(a, bb)
    return a


def pdiv(a, f):
    """quotient of a by f (exact division assumed)."""
    a = a[:]
    df = len(f) - 1
    iv = inv(f[-1])
    q = [0] * max(len(a) - df, 1)
    for sh in range(len(a) - 1 - df, -1, -1):
        cf = mul(a[sh + df], iv)
        q[sh] = cf
        if cf:
            for i, c in enumerate(f):
                if c:
                    a[sh + i] ^= mul(cf, c)
    return q


def degree_pattern(f):
    """degrees of the irreducible factors of a squarefree f over GF(2^8) (distinct degree factorization); None if not squarefree."""
    d = len(f) - 1
    der = [f[i] if i & 1 else 0 for i in range(1, len(f))]
    if not any(der):
        return None
    g = pgcd(f, der)
    if len(g) > 1:
        return None
    pat = []
    h = [0, 1]
    cur = f[:]
    k = 0
    while len(cur) - 1 >= 2 * (k + 1):
        k += 1
        for _ in range(8):
            h = pmulmod(h, h, cur)
        hx = h[:] + [0] * max(0, 2 - len(h))
        hx[1] ^= 1
        g = pgcd(cur, hx)
        dg = len(g) - 1
        if dg > 0:
            pat += [k] * (dg // k)
            cur = pdiv(cur, g)
            if len(cur) > 1:
                h = pmod(h, cur)
    if len(cur) > 1:
        pat.append(len(cur) - 1)
    return sorted(pat)


def subset_sums(pat):
    s = {0}
    for d in pat:
        s |= {x + d for x in s}
    return s


def abs_irreducible(G, rng, forbidden_tau, tries=3, lines=60):
    """probabilistic certificate that G (jet form) is absolutely irreducible over F(tau).  Returns True / False(not certified)."""
    # back to (tau, u, v): Y0 = u + X v, Y1 = v ; specialise X = x0 (tau0 = x0^2)
    delta = max(a + e for (_, a, e) in G)
    for _ in range(tries):
        x0 = rng.randrange(1, 256)
        if mul(x0, x0) in forbidden_tau:
            continue
        # g(u, v) = sum coeff x0^x (u + x0 v)^a v^e
        g = {}
        for (x, a, e), val in G.items():
            cx = mul(val, fpow(x0, x))
            if not cx:
                continue
            for t in range(a + 1):
                if binom2(a, t):
                    key = (a - t, e + t)
                    g[key] = g.get(key, 0) ^ mul(cx, fpow(x0, t))
        g = {key: v for key, v in g.items() if v}
        if not g or max(i + k for (i, k) in g) < delta:
            continue
        possible = set(range(1, delta))          # sizes of a proper factor still compatible with all lines
        for _l in range(lines):
            u0, v0, u1, v1 = (rng.randrange(256) for _ in range(4))
            if u1 == 0 and v1 == 0:
                continue
            f = [0] * (delta + 1)
            for (i, k), val in g.items():
                # (u0 + u1 s)^i (v0 + v1 s)^k
                pu = [mul(binom2(i, t), mul(fpow(u0, i - t), fpow(u1, t))) for t in range(i + 1)]
                pv = [mul(binom2(k, t), mul(fpow(v0, k - t), fpow(v1, t))) for t in range(k + 1)]
                for t1, c1 in enumerate(pu):
                    if c1:
                        for t2, c2 in enumerate(pv):
                            if c2:
                                f[t1 + t2] ^= mul(val, mul(c1, c2))
            if f[delta] == 0:
                continue
            pat = degree_pattern(f)
            if pat is None:
                continue
            possible &= subset_sums(pat)
            if not possible:
                break
        if possible:
            continue
        # a nonsingular rational point
        for _p in range(4000):
            u0, v0 = rng.randrange(256), rng.randrange(256)
            val = gu = gv = 0
            for (i, k), cf in g.items():
                val ^= mul(cf, mul(fpow(u0, i), fpow(v0, k)))
                if i & 1:
                    gu ^= mul(cf, mul(fpow(u0, i - 1), fpow(v0, k)))
                if k & 1:
                    gv ^= mul(cf, mul(fpow(u0, i), fpow(v0, k - 1)))
            if val == 0 and (gu or gv):
                return True
    return False


# ------------------------------------------------------------------ sections (Lemma 0 of note 35 and Theorem 3.4)
PLANT = []


def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        r[i] ^= x
    for i, x in enumerate(b):
        r[i] ^= x
    return r


def pmul(a, b):
    if not a or not b:
        return [0]
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for k, z in enumerate(b):
                if z:
                    r[i + k] ^= mul(x, z)
    return r


def ppow_table(P, kmax):
    out = [[1]]
    for _ in range(kmax):
        out.append(pmul(out[-1], P))
    return out


def section_data(G, P):
    """q0 = G(X, P, P') and q1 = (dG/dY1)(X, P, P') as coefficient lists."""
    dP = [P[i] if i & 1 else 0 for i in range(1, len(P))] or [0]
    amax = max(a for (_, a, _) in G)
    emax = max(e for (_, _, e) in G)
    Pp, dPp = ppow_table(P, amax), ppow_table(dP, emax)
    q0, q1 = [0], [0]
    for (x, a, e), val in G.items():
        base = [0] * x + [mul(val, c) for c in Pp[a]]
        q0 = padd(q0, pmul(base, dPp[e]))
        if e & 1:
            q1 = padd(q1, pmul(base, dPp[e - 1]))
    return q0, q1


def root_order(q, al):
    """multiplicity of al as a root of q (q nonzero)."""
    q = q[:]
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    k = 0
    while any(q):
        # synthetic division by (X - al)
        r = 0
        out = [0] * (len(q) - 1) if len(q) > 1 else []
        for i in range(len(q) - 1, -1, -1):
            r = mul(r, al) ^ q[i]
            if i > 0:
                out[i - 1] = r
        if r:
            break
        k += 1
        q = out
        if not q:
            break
    return k


def check_sections(kernel, wb, pts, prof, Dc, n):
    P = PLANT[0]
    agree = [i for i, (al, yy) in enumerate(pts) if lib.peval(P, al) == yy]
    AP = len(agree)
    s0 = sum(2 * prof[i] for i in agree)                         # Lemma 0: section as soon as W < s0
    s1 = Dc + sum(max(2 * prof[i] - 1, 0) for i in agree)        # Theorem 3.4: a regular section needs W >= s1
    nsec = nreg = nsing = bad = 0
    for w, cf in kernel:
        G = to_jet(wb, cf)
        q0, q1 = section_data(G, P)
        is_sec = not any(q0)
        if w < s0 and not is_sec:
            bad += 1
        if is_sec:
            nsec += 1
            if any(q1):
                nreg += 1
                dq = max(i for i, c in enumerate(q1) if c)
                if dq > w - Dc or w < s1:
                    bad += 1
                for i in agree:
                    if prof[i] and root_order(q1, pts[i][0]) < 2 * prof[i] - 1:
                        bad += 1
                        break
            else:
                nsing += 1
                if max(e for (_, _, e) in G) >= 1 and w >= s1 and False:
                    pass
    print(f"  planted polynomial: {AP} agreements; Lemma 0 threshold {s0}, bound (J) for a regular section {s1}; of {len(kernel)} basis solutions "
          f"{nsec} have it as a section ({nreg} regular, {nsing} singular); violations of Lemma 0 / Theorem 3.4: {bad}")


# ------------------------------------------------------------------ driver
def parse(argv):
    opt = {"word": "rand", "dom": "sub", "x": "1", "jrest": "0", "seed": "1", "irr": "1"}
    for a in argv:
        if "=" in a:
            k, v = a.split("=", 1)
            opt[k] = v
    return opt


def make_instance(N, opt):
    n = 1 << N
    seed = int(opt["seed"])
    rng = random.Random(1000 + seed)
    Dc = int(opt.get("D", n // 2 - 1))
    if opt["dom"] == "sub":
        D = lib.subspace_domain(N, seed=seed + 2)
    else:
        D = rng.sample(range(256), n)
    wd = opt["word"]
    if wd == "rand":
        y = [rng.randrange(256) for _ in D]
    elif wd == "fam":
        y = [fpow(al, 3 * n // 4 - 1) for al in D]
    elif wd == "zero":
        y = [0 for _ in D]
    elif wd.startswith("mono:"):
        y = [fpow(al, int(wd[5:])) for al in D]
    elif wd.startswith("plant:"):
        P = [rng.randrange(256) for _ in range(Dc + 1)]
        PLANT.append(P)
        y = [lib.peval(P, al) for al in D]
        for pos in rng.sample(range(n), int(wd[6:])):
            y[pos] ^= rng.randrange(1, 256)
    elif wd == "two":
        P1 = [rng.randrange(256) for _ in range(Dc + 1)]
        P2 = [rng.randrange(256) for _ in range(Dc + 1)]
        y = [lib.peval(P1 if i % 2 == 0 else P2, al) for i, al in enumerate(D)]
    else:
        raise SystemExit("unknown word")
    return n, Dc, D, y, rng


def minima_from_kernel(kernel):
    """successive minima: the weights W at which the number of solutions of leading weight exactly W exceeds the number at W - 2."""
    cnt = {}
    for w, _ in kernel:
        cnt[w] = cnt.get(w, 0) + 1
    mins = []
    for w in sorted(cnt):
        new = cnt[w] - cnt.get(w - 2, 0)
        mins += [w] * max(new, 0)
    return mins


def main():
    if len(sys.argv) < 4:
        raise SystemExit(__doc__)
    N, b, j = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    opt = parse(sys.argv[4:])
    n, Dc, D, y, rng = make_instance(N, opt)
    x = float(opt["x"])
    jrest = int(opt["jrest"])
    n1 = round(x * n)
    prof = [j] * n1 + [jrest] * (n - n1)
    pts = list(zip(D, y))
    # number of conditions and the mean of the minima (conservation law), to choose Wmax
    def conds(bb, jj):
        tot = 0
        for Nn in range(0, 2 * jj):
            if Nn % 2 == 0:
                e = max(0, jj - Nn // 2)
                tot += (bb + 1) * (Nn // 2 + 1) - max(bb - 2 * e + 1, 0) * max(Nn // 2 - e + 1, 0)
            else:
                e = max(0, jj - (Nn + 1) // 2)
                tot += bb * ((Nn - 1) // 2 + 1) - max(bb - 2 * e, 0) * max((Nn - 1) // 2 - e + 1, 0)
        return tot
    kappa = n1 * conds(b, j) + (n - n1) * (conds(b, jrest) if jrest else 0)
    wmax = int(float(opt["wmax"]) * n) if "wmax" in opt else None
    if wmax is None:
        # rough: the mean of the minima is about (sum of base weights + 2 kappa) / rank; iterate on the rank
        Wg = (b + 2) * Dc + n1 * (j - 1) + (n - n1) * max(jrest - 1, 0)
        for _ in range(40):
            base = [w for (w, t, i, k, c0) in make_basis(b, Dc, Wg) if i == 0]
            mean = (sum(base) + 2 * kappa) / len(base)
            if mean + 4 <= Wg:
                break
            Wg = int(mean) + 6
        wmax = Wg
    print(f"n = {n}, D = {Dc}, dom = {opt['dom']}, word = {opt['word']}, b <= {b}, contact {2*j} on {n1} lines, {2*jrest} on {n - n1}, "
          f"A = ceil(0.7 n) = {-(-7 * n // 10)}, W explored up to {wmax} = {wmax / n:.3f} n")
    wb, kernel, rk = solve(pts, prof, b, Dc, wmax)
    print(f"  basis {len(wb)}, rank of the conditions {rk}; expected (Corollary 2.4) {kappa}{'' if rk == kappa else '  (not reached at this W, or dependent)'}")
    mins = minima_from_kernel(kernel)
    base = sorted(w for (w, t, i, k, c0) in wb if i == 0)
    law = sum(base) + 2 * kappa
    full = len(mins) == len(base)
    print(f"  successive minima found: {mins}")
    print(f"  rank of the lattice {len(base)}; conservation law sum = {law}: " +
          (f"sum found {sum(mins)} {'OK' if sum(mins) == law else 'MISMATCH'}" if full else f"only {len(mins)} minima below {wmax}, partial sum {sum(mins)}"))
    # checks on every kernel vector
    nfail = 0
    first_b = {}
    first_II = {}
    for w, cf in kernel:
        G = to_jet(wb, cf)
        bb, db, W, fails = check_solution(G, pts, prof, Dc)
        assert W == w
        if fails:
            nfail += 1
            if nfail <= 3:
                print("   FAILED CHECK:", fails[:4])
        if bb not in first_b:
            first_b[bb] = W
        if db >= 2 and bb not in first_II:
            first_II[bb] = (W, db)
    print(f"  checks of Lemma 2.1, Corollary 2.3, the fibre statement, the content and (L1) on {len(kernel)} basis solutions: "
          f"{'all pass' if nfail == 0 else str(nfail) + ' FAIL'}")
    for bb in sorted(first_b):
        print(f"  smallest W with a solution of Y1-degree exactly {bb} in the basis: {first_b[bb]} = {first_b[bb] / n:.3f} n")
    if PLANT:
        check_sections(kernel, wb, pts, prof, Dc, n)
    # case II at exact Y1-degree b: the first W at which the solution space contains an element with Y1-degree b and
    # leading coefficient involving Y0 (linear condition on the space: some basis vector has such a top block)
    topII = [m for m, (w, t, i, k, c0) in enumerate(wb) if k >= 1 and ((t == 0 and c0 == b) or (t == 1 and c0 == b - 1))]
    WII = None
    for w, cf in kernel:
        if any(cf[m] for m in topII):
            WII = w
            break
    S1 = sum(max(jj - 1, 0) for jj in prof)
    l1min = min((b + d) * Dc + sum(max(jj - d // 2, 2 * jj - b - d, 0) for jj in prof) for d in range(2, 2 * j + 6, 2))
    A = -(-7 * n // 10)
    agree_min = sorted(max(2 * jj - 1, 0) for jj in prof)[:A]
    print(f"  W_II(b = {b}) = {WII} = {WII / n if WII else float('nan'):.3f} n;   bound (L1), minimum over d: {l1min} = {l1min / n:.3f} n "
          f"((b+2) D + sum (j-1)_+ = {(b + 2) * Dc + S1});   bound (J) at A = ceil(0.7 n): D + sum of the A smallest (2j-1)_+ = {Dc + sum(agree_min)} = {(Dc + sum(agree_min)) / n:.3f} n")
    if WII is not None and WII < l1min:
        print("   VIOLATION of (L1)")
    if opt["irr"] == "1" and WII is not None:
        forb = {mul(al, al) for al in D}
        Wirr = None
        tested = []
        for Wt in sorted({w for w, _ in kernel if w >= WII}):
            vecs = [cf for w, cf in kernel if w <= Wt]
            ok = False
            for _try in range(2):
                comb = [0] * len(wb)
                for cf in vecs:
                    s = rng.randrange(1, 256)
                    comb = [a ^ mul(s, c) if c else a for a, c in zip(comb, cf)]
                G = to_jet(wb, comb)
                bb = max(e for (_, _, e) in G)
                if bb != b:
                    continue
                if abs_irreducible(G, rng, forb):
                    ok = True
                    delta = max(a + e for (_, a, e) in G)
                    db = max(a for (xx, a, e) in G if e == b)
                    nondeg = None
                    if b >= 2:
                        # gcd of the coefficients of Y1^(b-1) and Y1^b at random X = x0 (coprime there => coprime over F(X))
                        nondeg = False
                        for _g in range(4):
                            x0 = rng.randrange(1, 256)
                            if x0 in D:
                                continue
                            f1 = [0] * (delta + 1)
                            f2 = [0] * (delta + 1)
                            for (xx, a, e), val in G.items():
                                if e == b - 1:
                                    f1[a] ^= mul(val, fpow(x0, xx))
                                elif e == b:
                                    f2[a] ^= mul(val, fpow(x0, xx))
                            while len(f1) > 1 and f1[-1] == 0:
                                f1.pop()
                            while len(f2) > 1 and f2[-1] == 0:
                                f2.pop()
                            if any(f1) and any(f2) and len(pgcd(f1, f2)) == 1:
                                nondeg = True
                                break
                    break
            tested.append(Wt)
            if ok:
                Wirr = (Wt, delta, db, len(vecs))
                break
            if len(tested) >= 12:
                break
        if Wirr:
            print(f"  W_irr = {Wirr[0]} = {Wirr[0] / n:.3f} n: a random combination of the {Wirr[3]} solutions of weighted degree <= {Wirr[0]} is absolutely "
                  f"irreducible, (u,v)-degree {Wirr[1]}, deg_Y0 of the leading coefficient {Wirr[2]}" +
                  ("" if nondeg is None else f"; coefficients of Y1^{b-1} and Y1^{b} coprime: {'yes' if nondeg else 'NO (degenerate)'}"))
        else:
            print(f"  no absolutely irreducible random combination certified for W in {tested}")
    sys.stdout.flush()


if __name__ == "__main__":
    main()
