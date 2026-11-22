#!/usr/bin/env python3
"""54_lemmaB_thm4.py: falsification tests of Lemma B (note 40), Proposition 1 and Theorem 4 (note 45) with the
extension of note 51 to every contact order, Lemma N and Lemma M (note 40), Corollary F part 1 (note 48).

Exact arithmetic over GF(2^16) (54_gf.py).  For a set of points, a word and a prescribed contact profile (j_alpha),
the potentials E (modulo F[X^2, Y^2]) whose first integral dE = E_X + Y1 E_Y has contact order >= 2 j_alpha on the
line of alpha are the solutions of a linear system (the Taylor coefficients e_rq of E at the received point with
r + q < 2j, (r, q) not both even, vanish).  The script finds the smallest weighted degree W with a solution, takes
random solutions there and a little above, and then measures everything FROM THE DEFINITIONS:

  * the contact order at every point, from the definition of the contact ideal (expansion of dE in T^i w^l Y1^e,
    w = S - T Y1, minimum of i + 2l); it does not use the criterion that built the system;
  * W = weighted degree of dE, D_a = deg_Y E_Y, D_c = deg_Y E_X;
  * Res_Y(E_Y, E_X) in F[X] (Sylvester determinant, evaluation and interpolation), its degree and its order at alpha;
  * the conics A, B, C of note 45, det E, its degree and its order at alpha, the orders of B, A + xi B, C + zeta B.

and compares with every inequality.  Any violation is printed with the word VIOLATION and counted.

Run:  python3 54_lemmaB_thm4.py [quick]
"""
import sys
import random
import time
from importlib import import_module

gf = import_module("54_gf")
mul, inv, fpow, fsqrt = gf.mul, gf.inv, gf.fpow, gf.fsqrt
binom2 = gf.binom2

VIOL = []


def support(W, D, shape):
    """monomials X^i Y^k of E, (i, k) not both even, with wdeg(dE) <= W for the weights (1, D, D).
    shape = (Ka, Dc) or None: deg_Y E_Y <= 2 Ka and deg_Y E_X <= Dc."""
    Ka, Dc = shape if shape else (10 ** 6, 10 ** 6)
    monos = []
    k = 0
    while D * k <= W + 1:
        for i in range(0, W + 2 - D * k):
            if k & 1:
                if i + D * k > W or k - 1 > 2 * Ka:
                    continue
                if (i & 1) and k > Dc:
                    continue
                monos.append((i, k))
            elif i & 1:
                if i - 1 + D * k > W or k > Dc:
                    continue
                monos.append((i, k))
        k += 1
    return monos


def conditions(pts, ys, prof):
    out = []
    for al, y, j in zip(pts, ys, prof):
        for r in range(2 * j):
            for q in range(2 * j - r):
                if (r & 1) or (q & 1):
                    out.append((al, y, r, q))
    return out


def system(monos, conds):
    rows = []
    for al, y, r, q in conds:
        row = [0] * len(monos)
        for idx, (i, k) in enumerate(monos):
            if i >= r and k >= q and binom2(i, r) and binom2(k, q):
                row[idx] = mul(fpow(al, i - r), fpow(y, k - q))
        rows.append(row)
    return rows


def wdeg_dE(E, D):
    W = -1
    for (i, k), c in E.items():
        if not c:
            continue
        if k & 1:
            W = max(W, i + D * k)
        if i & 1:
            W = max(W, i - 1 + D * k)
    return W


def contact_order(a_t, c_t, cap):
    """order of c + a Y1 in the contact ideal, from the definition: substitute S = w + T Y1 and take the minimum
    of i + 2l over the monomials T^i w^l Y1^e; exact when the result is <= cap (the Taylor dicts go up to r + q = cap)."""
    coef = {}
    for shift, t in ((0, c_t), (1, a_t)):
        for (r, q), v in t.items():
            for p in range(q + 1):
                if binom2(q, p):
                    key = (r + p, q - p, p + shift)
                    coef[key] = coef.get(key, 0) ^ v
    return min((i + 2 * l for (i, l, e), v in coef.items() if v), default=cap + 1)


def resultant_Y(a, c):
    ac, cc = gf.ycoeffs(a), gf.ycoeffs(c)
    Da, Dc = len(ac) - 1, len(cc) - 1
    if Da < 0 or Dc < 0:
        return None, Da, Dc
    if Da == 0 and Dc == 0:
        return [1], Da, Dc
    bound = Dc * max(len(p) - 1 for p in ac if p) + Da * max(len(p) - 1 for p in cc if p)
    xs = list(range(1, bound + 2))
    n = Da + Dc
    vals = []
    for x in xs:
        av = [gf.peval(p, x) for p in ac]
        cv = [gf.peval(p, x) for p in cc]
        mat = []
        for i in range(Dc):
            row = [0] * n
            for k in range(Da + 1):
                row[i + (Da - k)] = av[k]
            mat.append(row)
        for i in range(Da):
            row = [0] * n
            for k in range(Dc + 1):
                row[i + (Dc - k)] = cv[k]
            mat.append(row)
        vals.append(gf.det(mat))
    return gf.pinterp(xs, vals), Da, Dc


def conics(E):
    """A, B, C with E = Theta^2 + Y A^2 + X C^2 + X Y B^2 (dict polynomials)."""
    A, B, C = {}, {}, {}
    for (i, k), c in E.items():
        if not c:
            continue
        s = fsqrt(c)
        if (i & 1) and (k & 1):
            B[((i - 1) // 2, (k - 1) // 2)] = s
        elif k & 1:
            A[(i // 2, (k - 1) // 2)] = s
        elif i & 1:
            C[((i - 1) // 2, k // 2)] = s
    return A, B, C


def lincomb(P, Q, s):
    out = dict(P)
    for key, v in Q.items():
        out[key] = out.get(key, 0) ^ mul(s, v)
    return {k: v for k, v in out.items() if v}


def det3(rows):
    (a, b, c), (d, e, f), (g, h, i) = rows
    pm, pa = gf.pmul, gf.padd
    t = pm(a, pa(pm(e, i), pm(f, h)))
    t = pa(t, pm(b, pa(pm(d, i), pm(f, g))))
    t = pa(t, pm(c, pa(pm(d, h), pm(e, g))))
    return t


def rhoK(K, j):
    return max(j - K, 2 * j - 1 - 2 * K, 0)


def content(E):
    """gcd in F[X] of all the coefficients (in Y) of E_Y and E_X: the content of dE = E_X + Y1 E_Y."""
    g = []
    for P in (gf.dY(E), gf.dX(E)):
        for p in gf.ycoeffs(P):
            if p:
                g = gf.pgcd(g, p) if g else p[:]
    return g


def divide_content(E, g):
    """E / g; g is the content of dE, a polynomial in X^2 (the content of G in F[tau]), and it divides E coefficientwise."""
    assert all(cf == 0 for cf in g[1::2]), "content is not a polynomial in X^2"
    out = {}
    cols = {}
    for (i, k), cf in E.items():
        if cf:
            cols.setdefault(k, {})[i] = cf
    for k, col in cols.items():
        p = [0] * (max(col) + 1)
        for i, cf in col.items():
            p[i] = cf
        q, r = gf.pdivmod(p, g)
        assert not r, "content does not divide E"
        for i, cf in enumerate(q):
            if cf:
                out[(i, k)] = cf
    return out


STATS = {"sudan": 0, "nine": 0, "analysed": 0, "primitive_coprime": 0, "nonprimitive": 0, "Bfail_nonprimitive": 0, "det_raw": 0, "det_raw_high": 0, "det_raw_tight": 0}


def det_raw(name, E, pts, ys, D, cap):
    """Theorem 4 with its extension as an algebraic statement about ANY quintic potential (primitive or not):
    (X - alpha)^(3j - 4) divides det E at a line of contact 2j >= 4, and deg det E <= (3W - 8 Delta - 1)/2."""
    A, B, C = conics(E)
    yd = lambda P: max((k for (_, k) in P), default=-1)
    if max(yd(A), yd(B), yd(C)) > 2:
        return
    rows = []
    for P in (A, B, C):
        yc = gf.ycoeffs(P)
        rows.append([yc[k] if k < len(yc) else [] for k in range(3)])
    dE = det3(rows)
    if not dE:
        return
    a, c = gf.dY(E), gf.dX(E)
    W = wdeg_dE(E, D)
    STATS["det_raw"] += 1
    if 2 * gf.pdeg(dE) > 3 * W - 8 * D - 1:
        print("      VIOLATION: THEOREM 4 degree on the non-primitive potential")
        VIOL.append((name, "Theorem 4 degree, raw"))
    for al, y in zip(pts, ys):
        j = contact_order(gf.taylor(a, al, y, cap), gf.taylor(c, al, y, cap), cap) // 2
        if j >= 4:
            o = gf.pord(dE, al)
            STATS["det_raw_high"] += 1
            STATS["det_raw_tight"] += (o == 3 * j - 4)
            if o < 3 * j - 4:
                print("      VIOLATION: THEOREM 4 extension: ord det E = %d < 3j - 4 = %d at contact %d" % (o, 3 * j - 4, 2 * j))
                VIOL.append((name, "Theorem 4 extension, raw"))


def lemmaB_raw(E, pts, ys, D, cap):
    """does the inequality of Lemma B hold for this E as it is (used to show that primitivity is needed)?"""
    a, c = gf.dY(E), gf.dX(E)
    if not a or not c:
        return None
    res, Da, Dc = resultant_Y(a, c)
    if not res:
        return None
    W = wdeg_dE(E, D)
    tot = 0
    for al, y in zip(pts, ys):
        o = contact_order(gf.taylor(a, al, y, cap), gf.taylor(c, al, y, cap), cap)
        tot += max(o * o - o - 1, 0) if o >= 2 else 0
    return tot <= Dc * (W - D) + Da * W - D * Da * Dc, tot, Dc * (W - D) + Da * W - D * Da * Dc


def analyze(name, E, pts, ys, D, want, verbose=True, planted=()):
    """all measurements and all comparisons for one potential E."""
    a, c = gf.dY(E), gf.dX(E)
    W = wdeg_dE(E, D)
    if not a:
        print("    %s: E_Y = 0 (b = 0), skipped" % name)
        return None
    STATS["analysed"] += 1
    g = content(E)
    if gf.pdeg(g) > 0:
        raw = lemmaB_raw(E, pts, ys, D, 2 * max(want) + 6)
        STATS["nonprimitive"] += 1
        msg = ""
        if raw is not None:
            ok, tot, bd = raw
            msg = "; BEFORE division the inequality of Lemma B %s (sum = %d, bound %d)" % ("holds" if ok else "FAILS", tot, bd)
            if not ok:
                STATS["Bfail_nonprimitive"] += 1
        print("    %s: dE has content of degree %d in X (W = %d)%s; analysing the primitive part" % (name, gf.pdeg(g), W, msg))
        det_raw(name, E, pts, ys, D, 2 * max(want) + 6)
        E = divide_content(E, g)
        a, c = gf.dY(E), gf.dX(E)
        W = wdeg_dE(E, D)
        want = [0] * len(pts)
        assert gf.pdeg(content(E)) == 0
    ac, cc = gf.ycoeffs(a), gf.ycoeffs(c)
    Da, Dc = len(ac) - 1, len(cc) - 1
    K = Da // 2
    delta = max(Da + 1, Dc)
    cap = 2 * max(want) + 6
    js, bad = [], []
    for al, y in zip(pts, ys):
        a_t, c_t = gf.taylor(a, al, y, cap), gf.taylor(c, al, y, cap)
        o = contact_order(a_t, c_t, cap)
        if o > cap:
            bad.append("contact order above the cap at a point")
            o = cap
        if o & 1:
            bad.append("odd contact order %d" % o)
        j = o // 2
        js.append(j)
        ma = min((r + q for (r, q) in a_t), default=cap + 1)
        mc = min((r + q for (r, q) in c_t), default=cap + 1)
        if j >= 1 and (ma < 2 * j - 1 or mc < 2 * j - 1):
            bad.append("Lemma N: mult a = %d, mult c = %d < 2j - 1 = %d" % (ma, mc, 2 * j - 1))
        # criterion of note 40, Proposition 9 part 1, both directions: j is the largest j' with a, c in m^(2j'-1)
        jcrit = (min(ma, mc) + 1) // 2
        if jcrit != j:
            bad.append("criterion: contact order %d but min mult of (a, c) = %d" % (o, min(ma, mc)))
        # Corollary F part 1
        for k2, p in enumerate(ac):
            if p and gf.pord(p, al) < rhoK(K, j):
                bad.append("Corollary F: ord of the coefficient of Y^%d is %d < rho_K = %d" % (k2, gf.pord(p, al), rhoK(K, j)))
    if any(j < w for j, w in zip(js, want)):
        bad.append("solution has less contact than imposed: %s < %s" % (js, list(want)))
    prof = {}
    for j in js:
        prof[j] = prof.get(j, 0) + 1
    beta = lambda j: max(4 * j * j - 2 * j - 1, 0)
    sumbeta = sum(beta(j) for j in js)
    # ---- Lemma B
    res, _, _ = resultant_Y(a, c) if c else (None, Da, -1)
    line = "    %s: W = %d, D_a = %d, D_c = %d, profile %s" % (name, W, Da, Dc, " ".join("%dx(j=%d)" % (v, k) for k, v in sorted(prof.items())))
    if not c:
        line += "; E_X = 0"
    elif not res:
        line += "; Res = 0 (E_Y, E_X not coprime: not absolutely irreducible, Lemma B does not apply)"
    else:
        dres = gf.pdeg(res)
        degbound = Dc * (W - D) + Da * W - D * Da * Dc
        ords = [gf.pord(res, al) for al in pts]
        tight = sum(1 for o, j in zip(ords, js) if j >= 1 and o == beta(j))
        ncont = sum(1 for j in js if j >= 1)
        line += "; deg Res = %d <= %d; sum(o^2-o-1) = %d; local orders equal to the bound at %d of %d contained lines" % (dres, degbound, sumbeta, tight, ncont)
        for o, j, al in zip(ords, js, pts):
            if o < beta(j):
                bad.append("LEMMA B local: ord Res = %d < o^2 - o - 1 = %d at a line of contact %d" % (o, beta(j), 2 * j))
        if dres > degbound:
            bad.append("LEMMA B degree: deg Res = %d > %d" % (dres, degbound))
        if sumbeta > degbound:
            bad.append("LEMMA B: sum = %d > %d" % (sumbeta, degbound))
        if (Da + Dc) * W < D * Dc * (1 + Da) + sumbeta:
            bad.append("LEMMA B linear form violated")
        STATS["primitive_coprime"] += 1
        if max(js) > delta:
            bad.append("Lemma M: j = %d > delta = %d" % (max(js), delta))
        if max(js) > max(K, (Dc + 1) // 2):
            bad.append("Lemma M' (referee): j = %d > max(K, (D_c + 1) // 2) = %d" % (max(js), max(K, (Dc + 1) // 2)))
        if W < (2 * K + 1) * D + sum(rhoK(K, j) for j in js):
            bad.append("(L1) violated")
    # ---- Corollary F part 2 (the Sudan step behind (L2)) on the polynomials planted in the word
    for P in planted:
        aP = gf.subs_poly(a, P)
        if not aP:
            continue
        STATS["sudan"] += 1
        inS = [gf.peval(P, al) == y for al, y in zip(pts, ys)]
        need = D + sum(max(2 * j - 1, 0) if s_ else rhoK(K, j) for j, s_ in zip(js, inS))
        if gf.pdeg(aP) > W - D or W < need:
            bad.append("Corollary F part 2: W = %d < %d for a planted polynomial with %d agreements" % (W, need, sum(inS)))
    # ---- the last sentence of Lemma B in note 40 ("for W < 6 Delta the middle term is at most 9W - 25 Delta")
    if c and res and W < 6 * D and sumbeta > 9 * W - 25 * D:
        STATS["nine"] += 1
        line += "; NOTE: sum(o^2-o-1) = %d > 9W - 25 Delta = %d although W < 6 Delta" % (sumbeta, 9 * W - 25 * D)
    # ---- Proposition 1 of note 45 (every degree)
    A, B, C = conics(E)
    for al, y, j in zip(pts, ys, js):
        xi, ze = fsqrt(al), fsqrt(y)
        oB = gf.mult_at(B, al, y, cap) if B else cap + 1
        oA = gf.mult_at(lincomb(A, B, xi), al, y, cap)
        oC = gf.mult_at(lincomb(C, B, ze), al, y, cap)
        jp = min(oB + 1, oA, oC)
        if min(jp, cap // 2) != min(j, cap // 2):
            bad.append("PROPOSITION 1: contact 2j = %d but min(ord B + 1, ord(A + xi B), ord(C + zeta B)) = %d" % (2 * j, jp))
    # ---- Theorem 4 of note 45 and its extension (quintics: A, B, C conics)
    yd = lambda P: max((k for (_, k) in P), default=-1)
    if max(yd(A), yd(B), yd(C)) <= 2:
        rows = []
        for P in (A, B, C):
            yc = gf.ycoeffs(P)
            rows.append([yc[k] if k < len(yc) else [] for k in range(3)])
        dE = det3(rows)
        need = sum(3 * j - 4 for j in js if j >= 2)
        if not dE:
            line += "; det E = 0 (degenerate)"
        else:
            dd = gf.pdeg(dE)
            ords = [gf.pord(dE, al) for al in pts]
            tight = sum(1 for o, j in zip(ords, js) if j >= 2 and o == 3 * j - 4)
            n2 = sum(1 for j in js if j >= 2)
            line += "; deg det E = %d <= %s; sum(3j-4) = %d; orders equal to 3j-4 at %d of %d lines" % (dd, (3 * W - 8 * D - 1) / 2, need, tight, n2)
            for o, j in zip(ords, js):
                if j >= 2 and o < 3 * j - 4:
                    bad.append("THEOREM 4 local: ord det E = %d < 3j - 4 = %d at a line of contact %d" % (o, 3 * j - 4, 2 * j))
            if 2 * dd > 3 * W - 8 * D - 1:
                bad.append("THEOREM 4 degree: deg det E = %d > (3W - 8 Delta - 1)/2" % dd)
            if 3 * W < 8 * D + 1 + 2 * need:
                bad.append("THEOREM 4 (T) violated")
    if verbose:
        print(line)
    for b in bad:
        print("      VIOLATION: " + b)
        VIOL.append((name, b))
    return dict(W=W, Da=Da, Dc=Dc, js=js)


def make_word(kind, pts, D, rng):
    """returns (word, list of polynomials of degree <= D planted in it)."""
    n = len(pts)
    if kind == "rand":
        return [rng.randrange(1 << gf.M) for _ in pts], []
    if kind == "zero":
        return [0] * n, [[]]
    if kind.startswith("mono"):
        e = int(kind[4:])
        return [fpow(al, e) for al in pts], []
    if kind.startswith("plant"):
        # plantN: N codewords of degree <= D glued on consecutive blocks; plant1e: one codeword with random errors
        if kind == "plant1e":
            P = gf.rand_poly(rng, D)
            ys = [gf.peval(P, al) for al in pts]
            for i in rng.sample(range(n), n // 3):
                ys[i] ^= rng.randrange(1, 1 << gf.M)
            return ys, [P]
        N = int(kind[5:])
        Ps = [gf.rand_poly(rng, D) for _ in range(N)]
        return [gf.peval(Ps[(i * N) // n], al) for i, al in enumerate(pts)], Ps
    raise ValueError(kind)


def run_instance(tag, n, D, dom, word, prof, shape, seed, above=(0, 2)):
    rng = random.Random(seed)
    pts = gf.subspace(rng, n.bit_length() - 1) if dom == "sub" else gf.rand_points(rng, n)
    ys, planted = make_word(word, pts, D, rng)
    prof = list(prof)
    assert len(prof) == n
    conds = conditions(pts, ys, prof)
    t0 = time.time()
    cache = {}

    def null(W):
        if W not in cache:
            monos = support(W, D, shape)
            cache[W] = (monos, gf.nullspace(system(monos, conds), len(monos)) if monos else [])
        return cache[W]

    hi = D
    while len(support(hi, D, shape)) <= len(conds):
        hi += 1
    lo = 0
    # smallest W with a nonzero solution (the supports are nested)
    while lo < hi:
        mid = (lo + hi) // 2
        if null(mid)[1]:
            hi = mid
        else:
            lo = mid + 1
    Wmin = lo
    print("%s: n = %d, Delta = %d, %s points, word %s, imposed j = %s, shape %s: %d conditions, W_min = %d (nullity %d)  [%.1f s]"
          % (tag, n, D, "subspace" if dom == "sub" else "random", word, "".join(map(str, prof)) if max(prof) < 10 else prof,
             "free" if shape is None else "K<=%d, D_c<=%d" % shape, len(conds), Wmin, len(null(Wmin)[1]), time.time() - t0))
    for ab in above:
        monos, basis = null(Wmin + ab)
        if not basis:
            continue
        for trial in range(2 if ab else 1):
            vec = [0] * len(monos)
            for bvec in basis:
                s = rng.randrange(1, 1 << gf.M) if (len(basis) > 1 or ab) else 1
                for idx, v in enumerate(bvec):
                    if v:
                        vec[idx] ^= mul(s, v)
            E = {mo: v for mo, v in zip(monos, vec) if v}
            analyze("W_min+%d%s" % (ab, "ab"[trial] if ab else ""), E, pts, ys, D, prof, planted=planted)


def hand_example():
    """E = X^3 Y: E_Y = X^3 and E_X = X^2 Y are coprime in F(X)[Y], dE = X^2 (Y + X Y1) is not primitive."""
    E = {(3, 1): 1}
    a, c = gf.dY(E), gf.dX(E)
    D = 5
    o = contact_order(gf.taylor(a, 0, 0, 10), gf.taylor(c, 0, 0, 10), 10)
    res, Da, Dc = resultant_Y(a, c)
    W = wdeg_dE(E, D)
    print("hand example E = X^3 Y at the point (0, 0), Delta = %d: contact order %d, W = %d, Res_Y(E_Y, E_X) = X^%d, D_a = %d, D_c = %d:"
          % (D, o, W, gf.pdeg(res), Da, Dc))
    print("    o^2 - o - 1 = %d > D_c (W - Delta) + D_a W - Delta D_a D_c = %d: the inequality of Lemma B fails without primitivity\n"
          % (o * o - o - 1, Dc * (W - D) + Da * W - D * Da * Dc))
    assert o == 4 and o * o - o - 1 > Dc * (W - D) + Da * W - D * Da * Dc


def main():
    quick = len(sys.argv) > 1 and sys.argv[1] == "quick"
    t0 = time.time()
    hand_example()
    Q = (2, 5)        # quintic: K <= 2, D_c <= 5
    inst = [
        # the setting of the theorem, scaled: rate 1/2, contact 4 on all lines, quintic
        ("H1", 16, 8, "rnd", "rand", [2] * 16, Q, 1),
        ("H2", 16, 7, "sub", "rand", [2] * 16, Q, 2),
        ("H3", 16, 7, "sub", "mono11", [2] * 16, Q, 3),
        # mixed profiles, quintic
        ("Q1", 8, 4, "rnd", "rand", [3, 3, 2, 2, 2, 1, 1, 0], Q, 4),
        ("Q2", 8, 3, "rnd", "rand", [4, 3, 2, 2, 1, 1, 0, 0], Q, 5),
        ("Q3", 6, 3, "rnd", "rand", [5, 4, 3, 2, 2, 1], Q, 6),
        ("Q4", 4, 3, "rnd", "rand", [4, 4, 4, 4], Q, 7),
        ("Q5", 4, 2, "rnd", "rand", [5, 5, 4, 3], Q, 8),
        ("Q6", 8, 4, "sub", "rand", [3] * 8, Q, 9),
        ("Q7", 8, 4, "rnd", "plant2", [2, 2, 3, 2, 2, 2, 3, 1], Q, 10),
        ("Q8", 8, 4, "rnd", "zero", [2] * 8, Q, 11),
        ("Q9", 6, 5, "rnd", "rand", [5, 5, 3, 3, 2, 2], Q, 12),
        # cubic (K <= 1, D_c <= 3): the case that Lemma B closes in Theorem 2.1
        ("C1", 12, 6, "rnd", "rand", [1] * 12, (1, 3), 13),
        ("C2", 12, 6, "rnd", "rand", [2] * 6 + [1] * 6, (1, 3), 14),
        ("C3", 8, 4, "rnd", "rand", [3, 3, 2, 2, 1, 1, 1, 0], (1, 3), 15),
        ("C4", 16, 3, "sub", "mono7", [1] * 16, (1, 3), 16),
        ("C5", 32, 7, "sub", "mono15", [1] * 32, (1, 3), 161),      # the flat word of note 35 at rate 1/4
        # leading coefficient in F[X] (K = 0)
        ("K0a", 8, 4, "rnd", "rand", [2, 2, 2, 1, 1, 1, 1, 0], (0, 4), 17),
        ("K0b", 8, 4, "rnd", "rand", [3, 2, 2, 2, 1, 1, 0, 0], (0, 6), 18),
        # K = 1 with D_c = 5, 6; the sextic (K = 2, D_c = 6)
        ("K1a", 8, 4, "rnd", "rand", [3, 3, 2, 2, 2, 2, 1, 1], (1, 5), 19),
        ("K1b", 8, 4, "rnd", "rand", [4, 3, 3, 2, 2, 1, 1, 0], (1, 6), 20),
        ("S1", 8, 4, "rnd", "rand", [3, 3, 3, 2, 2, 2, 2, 1], (2, 6), 21),
        ("S2", 6, 3, "rnd", "rand", [6, 4, 3, 2, 2, 1], (2, 6), 22),
        # no restriction on the shape
        ("F1", 8, 3, "rnd", "rand", [2] * 8, None, 23),
        ("F2", 6, 2, "rnd", "rand", [4, 3, 3, 2, 1, 1], None, 24),
        ("F3", 8, 2, "sub", "rand", [3] * 8, None, 25),
        ("F4", 8, 3, "rnd", "plant1e", [3, 2, 2, 2, 2, 2, 1, 1], None, 26),
    ]
    if quick:
        inst = [i for i in inst if i[0] in ("Q1", "Q3", "C3", "K0a", "S2", "F2")]
    else:
        # rate 1/2 at n = 32 (the size of the checks of notes 40 and 45), contact 4 on all lines and a mixed profile
        inst.append(("H4", 32, 15, "sub", "rand", [2] * 32, Q, 27))
        inst.append(("H5", 32, 16, "rnd", "rand", [3] * 4 + [2] * 22 + [1] * 4 + [0] * 2, Q, 28))
        inst.append(("H6", 32, 15, "sub", "mono23", [2] * 32, Q, 29))
        # random profiles: quintic, cubic, sextic, K = 0, K = 1, and free shapes with contact up to 10
        rng = random.Random(54)
        shapes = [("rq", Q, 3), ("rc", (1, 3), 2), ("rs", (2, 6), 3), ("rk0", (0, 5), 3), ("rk1", (1, 6), 3), ("rf", None, 5), ("rq+", Q, 5)]
        for rep in range(8):
            for tag, shape, jmax in shapes:
                n = rng.choice([6, 8, 8, 12])
                D = rng.choice([2, 3, 4, 5]) if shape is None else rng.choice([3, 4, 5, 6])
                prof = [rng.choice(list(range(jmax + 1)) + [min(2, jmax)] * 2) for _ in range(n)]
                if shape is None and sum(j * j for j in prof) > 60:
                    prof = [min(j, 3) for j in prof]
                word = rng.choice(["rand", "rand", "rand", "plant2", "plant1e", "zero"])
                dom = "sub" if (n == 8 and rng.random() < 0.3) else "rnd"
                inst.append(("%s%d" % (tag, rep), n, D, dom, word, prof, shape, 1000 + 10 * rep + len(inst)))
    for it in inst:
        run_instance(*it)
    print("\n%d potentials analysed; %d with content (Lemma B's inequality fails before division for %d of them); %d primitive with coprime E_Y, E_X"
          % (STATS["analysed"], STATS["nonprimitive"], STATS["Bfail_nonprimitive"], STATS["primitive_coprime"]))
    print("Corollary F part 2 on planted polynomials: %d (potential, polynomial) pairs with E_Y(X, P) != 0" % STATS["sudan"])
    print("potentials with W < 6 Delta and sum(o^2-o-1) > 9W - 25 Delta (the last sentence of Lemma B in note 40 fails): %d" % STATS["nine"])
    print("Theorem 4 extension on non-primitive quintics with det E != 0: %d potentials, %d lines of contact >= 8, order of det E equal to 3j - 4 at %d of them"
          % (STATS["det_raw"], STATS["det_raw_high"], STATS["det_raw_tight"]))
    print("%d violations in all  [%.0f s]" % (len(VIOL), time.time() - t0))
    for v in VIOL:
        print("  ", v)


if __name__ == "__main__":
    main()
