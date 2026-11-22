#!/usr/bin/env python3
"""50_parity.py: the parity theorem of 50-residual-b-at-least-2.md, Section 1 (characteristic 2).

Even supports.  For q = 2^e and k >= 1 let S(q, k; m) be the monomials X^x Y0^a Y1^c with c in {0, q, ..., k q} and
x + Delta (a + c) < m A: polynomials in Y1^q of Y1-degree <= k q.  A nonzero R in S(q, k; m) with contact order m at every received
point satisfies R(X, P, P') = 0 for every P of degree <= Delta with >= A agreements (Lemma 0 of note 35), and every absolutely
irreducible first integral with Y1-degree b >= 1 divides R with a multiplicity divisible by q (Lemma 1.1).  So the first integrals
that can carry more than delta * d list members have b <= k (Theorem 1.3); for k = 1 only one component with b = 1 can.
Local rank of the contact conditions of order m on these supports in characteristic 2 (Lemma 1.2):
   k = 1:  rho_1(q, m) = m^2 - (q - 1) m + q (3q - 1)/2                       (m >= 2q)
   k = 2:  rho_2(q, m) = (3 m^2 - (6q - 3) m + 13 q^2 - 3q)/2                 (m >= 4q)
Certificate: |S(q, k; m)| > n rho_k(q, m).

Slack supports (Remark 1.5): S(m; s_0..s_B): X^x Y0^a Y1^c, c <= B, x + Delta (a + c) < (m - s_c) A + s_c Delta; rank <= R(m, B).

Parts:
  A  local ranks by exact linear algebra over GF(2) against the formulas (k = 1: q = 2, 4, 8; k = 2: q = 2, 4), and the same support
     {0, 2} over GF(3) (rank m^2 + 2: the gain is special to characteristic 2).
  B  exact thresholds of the even certificates, n = 2^25 .. 2^28, Delta = n/2 + 5; ranges of m and constants at selected agreements.
  C  thresholds of the slack supports (0,1,0), (0,1,0,1), (0,1,2,1,0), and of the full slack (1,1,1,1).
  D  toy checks over GF(2^8): (i) the flat word at rate 1/4 (n = 16): every element of the even explainer spaces {0, 2} and {0, 4}
     kills the jets of all 15 flats and equals lambda * (flat cubic)^q; (ii) planted words at rate 1/2: R kills the planted member;
     (iii) the half-slack space (0,1,0,1) on the flat word: Q and dQ/dY1 kill the flats, dQ/dY1 = lambda * (flat cubic)^2.
Run: python3 50_parity.py [A] [B] [C] [D]        (about 3 minutes; D is the long part)
"""
import sys
import random
from math import ceil, log2, isqrt
from fractions import Fraction
from importlib import import_module

c41 = import_module("41_counts")
loc = import_module("50_local")
R, N = c41.R, c41.N


def N0(Z, D):
    """number of (x, a) with x, a >= 0 and x + D a < Z."""
    return N(0, Z, D)


def rho(q, k, m):
    if k == 1:
        assert m >= 2 * q
        return m * m - (q - 1) * m + q * (3 * q - 1) // 2
    assert k == 2 and m >= 4 * q
    return (3 * m * m - (6 * q - 3) * m + 13 * q * q - 3 * q) // 2


def size_even(q, k, m, A, D):
    return sum(N0(m * A - i * q * D, D) for i in range(k + 1))


# ------------------------------------------------------------------ A
def rank_support(m, cs, p):
    """rank of {T^x S^a Y1^c : x + a < m, c in cs} in F_p[T, S, Y1] / c_m (graded computation, degree by degree)."""
    tot = 0
    B = max(cs)
    for Nn in range(0, m):
        gens = []
        for l in range(0, Nn + 1):
            i = Nn - l
            if i + 2 * l < m:
                continue
            for e in range(0, B + Nn + 1):
                gens.append(loc.expand(i, l, e, p))
        U = loc.reduce_space(gens, p, lambda mon: mon[2] not in cs)
        tot += len(cs) * (Nn + 1) - len(U)
    return tot


def part_A():
    print("A. local rank of the contact conditions of order m on even supports, exact linear algebra against the formulas of Lemma 1.2")
    ok = True
    for q, ms in ((2, range(4, 13)), (4, range(8, 15)), (8, (16, 17, 19))):
        row = [(m, rank_support(m, (0, q), 2), rho(q, 1, m)) for m in ms]
        ok &= all(r == f for (_, r, f) in row)
        print(f"   k = 1, q = {q}, GF(2): (m, rank, formula) = {row}")
    for q, ms in ((2, range(8, 13)), (4, (16, 17))):
        row = [(m, rank_support(m, (0, q, 2 * q), 2), rho(q, 2, m)) for m in ms]
        ok &= all(r == f for (_, r, f) in row)
        print(f"   k = 2, q = {q}, GF(2): (m, rank, formula) = {row}")
    row3 = [(m, rank_support(m, (0, 2), 3), m * m + 2) for m in range(4, 11)]
    print(f"   support {{0, 2}} over GF(3): (m, rank, m^2 + 2) = {row3}")
    full = [(m, rank_support(m, (0, 1, 2), 2), R(m, 2)) for m in range(4, 9)]
    print(f"   control, full support {{0, 1, 2}} over GF(2): (m, rank, R(m, 2)) = {full}")
    print(f"   all formulas confirmed: {ok and all(r == f for (_, r, f) in row3) and all(r == f for (_, r, f) in full)}")


# ------------------------------------------------------------------ B
def ms_even(q, k, A, n, D, mmax):
    return [m for m in range(2 * k * q, mmax + 1) if size_even(q, k, m, A, D) > n * rho(q, k, m)]


def part_B():
    print("B. even certificates |S(q, k; m)| > n rho_k(q, m): smallest agreement (exact integers, Delta = n/2 + 5, m <= 4000)")
    print("   the count is nondecreasing in A, so a certificate at A is a certificate at every larger A with the same m")
    for lg in (25, 26, 27, 28):
        n = 1 << lg
        D = n // 2 + 5
        john = isqrt(n * D)
        print(f"   n = 2^{lg}: Johnson radius: A^2 > n Delta iff A > {john} = {john / n:.7f} n")
        for k, qs in ((1, (2, 4, 8, 16, 32, 64, 128)), (2, (2, 4, 8, 16, 32, 64))):
            for q in qs:
                lo, hi = n // 2, john
                if not ms_even(q, k, hi, n, D, 4000):
                    print(f"      k = {k}, q = {q}: none at or below the Johnson radius")
                    continue
                while lo < hi:
                    mid = (lo + hi) // 2
                    if ms_even(q, k, mid, n, D, 4000):
                        hi = mid
                    else:
                        lo = mid + 1
                m0 = ms_even(q, k, lo, n, D, 4000)[0]
                print(f"      k = {k}, q = {q:<3}: A >= {lo} = {lo / n:.6f} n (m = {m0}, margin {size_even(q, k, m0, lo, D) - n * rho(q, k, m0)}, "
                      f"d = {(m0 * lo - 1) // D}); queries just above: {ceil(108 / log2(n / lo))}")
    print("   per agreement (n = 2^25 and n = 2^28 give the same ranges): the certificate with the smallest d = floor((mA - 1)/Delta)")
    for lg in (25, 28):
        n = 1 << lg
        D = n // 2 + 5
        for a in ("0.70", "0.7009", "0.7015", "0.702", "0.703", "0.7045", "0.705", "0.7055", "0.706", "0.7065", "0.707"):
            A = ceil(Fraction(a) * n)
            out = []
            for k in (1, 2):
                best = None
                for q in (2, 4, 8, 16, 32, 64, 128):
                    ms = ms_even(q, k, A, n, D, 2400)
                    if ms:
                        d = (ms[0] * A - 1) // D
                        if best is None or d < best[0]:
                            best = (d, q, ms[0], ms[-1])
                out.append(f"k = {k}: " + (f"q = {best[1]}, m in [{best[2]}, {best[3]}], d = {best[0]}, d^2 = {best[0] ** 2}" if best else "none"))
            print(f"      n = 2^{lg}, a = {a} (queries {ceil(108 / log2(n / A))}): " + "; ".join(out))

    print("   budget of a surviving component (Corollary 1.4): R = lambda * G^q forces q W(G) <= m A - 1 and q delta(G) <= d for every certificate;")
    print("   per agreement the minimum over q in {2, .., 512} (smallest m for each q) of floor((mA - 1)/q)/n and of floor(d/q), n = 2^25")
    n = 1 << 25
    D = n // 2 + 5
    for k, alist in ((1, ("0.7009", "0.7015", "0.702", "0.703", "0.7045", "0.705", "0.7055", "0.706", "0.7065", "0.707")), (2, ("0.70", "0.7009", "0.702", "0.703"))):
        for a in alist:
            A = ceil(Fraction(a) * n)
            bw = bd = None
            dmax = 0
            used = []
            for q in (2, 4, 8, 16, 32, 64, 128, 256, 512):
                ms = [m for m in range(2 * k * q, 6000) if size_even(q, k, m, A, D) > n * rho(q, k, m)][:1]
                if not ms:
                    continue
                m = ms[0]
                d = (m * A - 1) // D
                used.append((q, m, d))
                dmax = max(dmax, d)
                wv, dv = Fraction((m * A - 1) // q, n), d // q
                if bw is None or wv < bw[0]:
                    bw = (wv, q, m)
                if bd is None or dv < bd[0]:
                    bd = (dv, q, m)
            if bw:
                print(f"      k = {k}, a = {a}: certificates (q, smallest m, d): {used}; W < {float(bw[0]):.4f} n (q = {bw[1]}, m = {bw[2]}), "
                      f"delta <= {bd[0]} (q = {bd[1]}, m = {bd[2]}); all with d <= {dmax}")
            else:
                print(f"      k = {k}, a = {a}: no certificate")


# ------------------------------------------------------------------ C
SLACK = {"(0,1,0)": (0, 1, 0), "(0,1,0,1)": (0, 1, 0, 1), "(0,1,2,1,0)": (0, 1, 2, 1, 0), "(1,1,1,1) (full slack)": (1, 1, 1, 1)}


def size_slack(s, m, A, D):
    return sum(N0((m - sc) * A + sc * D - cc * D, D) for cc, sc in enumerate(s))


def part_C():
    print("C. slack supports (Remark 1.5): |S(m; s)| > n R(m, B)")
    for lg in (25, 28):
        n = 1 << lg
        D = n // 2 + 5
        john = isqrt(n * D)
        for name, s in SLACK.items():
            B = len(s) - 1

            def ms(A):
                return [m for m in range(max(s) + 2, 1501) if size_slack(s, m, A, D) > n * R(m, B)]
            lo, hi = n // 2, n
            while lo < hi:
                mid = (lo + hi) // 2
                if ms(mid):
                    hi = mid
                else:
                    lo = mid + 1
            print(f"   n = 2^{lg}, s = {name}: A >= {lo} = {lo / n:.6f} n (m = {ms(lo)[0]}), {'below' if lo <= john else 'ABOVE'} the Johnson radius; "
                  f"queries {ceil(108 / log2(n / lo))}")


# ------------------------------------------------------------------ D: toy checks over GF(2^8)
lib = import_module("40_lib")
mul, fpow, inv = lib.mul, lib.fpow, lib.inv


def binom2(a, b):
    return 1 if 0 <= b <= a and (b & ~a) == 0 else 0


def tmul3(p, q, m):
    out = {}
    for (i1, l1, e1), x1 in p.items():
        for (i2, l2, e2), x2 in q.items():
            if i1 + i2 + 2 * (l1 + l2) < m:
                key = (i1 + i2, l1 + l2, e1 + e2)
                v = out.get(key, 0) ^ mul(x1, x2)
                if v:
                    out[key] = v
                else:
                    out.pop(key, None)
    return out


def contact_rows(monos, al, y, m):
    """expansion of each monomial X^x Y0^a Y1^c at (al, y) in T^i w^l Y1^e, truncated at i + 2l < m (Y0 = y + w + T Y1)."""
    xmax = max(x for (x, a, c) in monos)
    amax = max(a for (x, a, c) in monos)
    xp = []
    for x in range(xmax + 1):
        d = {}
        for i in range(0, min(x, m - 1) + 1):
            if binom2(x, i):
                v = fpow(al, x - i)
                if v:
                    d[(i, 0, 0)] = v
        xp.append(d)
    base = {(0, 1, 0): 1, (1, 0, 1): 1}
    if y:
        base[(0, 0, 0)] = y
    yp = [{(0, 0, 0): 1}]
    for a in range(1, amax + 1):
        yp.append(tmul3(yp[-1], base, m))
    out = []
    for (x, a, c) in monos:
        e = tmul3(xp[x], yp[a], m)
        out.append({(i, l, ee + c): v for (i, l, ee), v in e.items()})
    return out


def explainer_space(D, y, monos, m):
    rows = {}
    for pi, (al, yy) in enumerate(zip(D, y)):
        for mi, e in enumerate(contact_rows(monos, al, yy, m)):
            for key, v in e.items():
                rows.setdefault((pi,) + key, {})[mi] = v
    mat = []
    for r in rows.values():
        b = bytearray(len(monos))
        for mi, v in r.items():
            b[mi] = v
        mat.append(bytes(b))
    return lib.nullspace(mat, len(monos))


def monos_even(q, k, m, A, Dc):
    out = []
    for i in range(k + 1):
        Z = m * A - i * q * Dc
        a = 0
        while Dc * a < Z:
            out += [(x, a, i * q) for x in range(Z - Dc * a)]
            a += 1
    return out


def monos_slack(s, m, A, Dc):
    out = []
    for cc, sc in enumerate(s):
        Z = (m - sc) * A + sc * Dc - cc * Dc
        a = 0
        while Dc * a < Z:
            out += [(x, a, cc) for x in range(Z - Dc * a)]
            a += 1
    return out


def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        r[i] ^= x
    for i, x in enumerate(b):
        r[i] ^= x
    return r


def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for k, z in enumerate(b):
                if z:
                    r[i + k] ^= mul(x, z)
    return r


def on_jet(Q, P, deriv=0):
    """Q(X, P, P') (deriv = 0) or (dQ/dY1)(X, P, P') (deriv = 1); Q a dict (x, a, c) -> value."""
    dP = [P[i] if i & 1 else 0 for i in range(1, len(P))] or [0]
    cp, cd = {0: [1]}, {0: [1]}
    out = [0]
    for (x, a, c), v in Q.items():
        if deriv and not (c & 1):
            continue
        cc = c - deriv
        for kk in range(1, a + 1):
            if kk not in cp:
                cp[kk] = pmul(cp[kk - 1], P)
        for kk in range(1, cc + 1):
            if kk not in cd:
                cd[kk] = pmul(cd[kk - 1], dP)
        out = padd(out, pmul([0] * x + [v], pmul(cp[a], cd[cc])))
    return out


def bmul(p, q):
    out = {}
    for (x1, a1), v1 in p.items():
        for (x2, a2), v2 in q.items():
            key = (x1 + x2, a1 + a2)
            out[key] = out.get(key, 0) ^ mul(v1, v2)
    return {key: v for key, v in out.items() if v}


def bpow(p, e):
    out = {(0, 0): 1}
    for _ in range(e):
        out = bmul(out, p)
    return out


def flat_setup(Nn, seed=1):
    n = 1 << Nn
    D = lib.subspace_domain(Nn, seed=seed + 2)
    y = [fpow(al, n // 2 - 1) for al in D]
    L = [1]
    for v in D:
        L = pmul(L, [v, 1])
    e = {j: L[1 << j] for j in range(Nn + 1)}
    assert all(L[i] == 0 for i in range(len(L)) if i & (i - 1)) and e[Nn] == 1
    # flat cubic of note 35, Proposition 5: dE = c + a Y1
    a = {(1, 2): 1, (0, 0): e[0]}
    c = {(0, 3): 1, (n // 2 - 2, 0): e[0]}
    for j in range(1, Nn):
        a[((1 << j) - 1, 0)] = a.get(((1 << j) - 1, 0), 0) ^ e[j]
        c[((1 << j) - 2, 1)] = c.get(((1 << j) - 2, 1), 0) ^ e[j]
    basis = []
    for al in D:
        if al and len(set(lib.span(basis + [al]))) == 2 ** (len(basis) + 1):
            basis.append(al)
        if len(basis) == Nn:
            break
    flats = []
    for mask in range(1, 1 << Nn):
        V = []
        for co in range(1 << Nn):
            if bin(co & mask).count("1") % 2 == 0:
                el = 0
                for kk in range(Nn):
                    if co >> kk & 1:
                        el ^= basis[kk]
                V.append(el)
        LV = [1]
        for v in V:
            LV = pmul(LV, [v, 1])
        P = LV[1:n // 2]
        assert sum(1 for al, yy in zip(D, y) if lib.peval(P, al) == yy) >= n // 2 - 1
        flats.append(P)
    return n, D, y, a, c, flats


def random_element(monos, null, rng):
    comb = [0] * len(monos)
    for vec in null:
        sc = rng.randrange(1, 256)
        comb = [x ^ mul(sc, b) if b else x for x, b in zip(comb, vec)]
    return {mo: v for mo, v in zip(monos, comb) if v}


def part_D():
    rng = random.Random(50)
    print("D. toy checks over GF(2^8)")
    print("   (i) the flat word alpha^(n/2 - 1), n = 16, Delta = 3, A = 7 (A^2 = 49 > n Delta = 48): 15 list members on the flat cubic dE = c + a Y1 (b = 1)")
    n, D, y, a, c, flats = flat_setup(4)
    for q, m in ((2, 9), (4, 12)):
        monos = monos_even(q, 1, m, 7, 3)
        null = explainer_space(D, y, monos, m)
        aq, cq = bpow(a, q), bpow(c, q)
        res = []
        for _ in range(2):
            Rr = random_element(monos, null, rng)
            bad = sum(1 for P in flats if any(on_jet(Rr, P)))
            R0 = {(x, aa): v for (x, aa, cc), v in Rr.items() if cc == 0}
            Rq = {(x, aa): v for (x, aa, cc), v in Rr.items() if cc == q}
            lhs, rhs = bmul(R0, aq), bmul(Rq, cq)
            prop = not any(lhs.get(key, 0) ^ rhs.get(key, 0) for key in set(lhs) | set(rhs))
            res.append((bad, bool(R0), bool(Rq), prop))
        print(f"       even support q = {q}, m = {m}: |S| = {len(monos)}, n rho = {n * rho(q, 1, m)}, space of dimension {len(null)}; two random elements R: "
              f"(flats with R != 0 on the jet, R_0 != 0, R_q != 0, R_0 a^q = R_q c^q) = {res}")
        sys.stdout.flush()
    s = (0, 1, 0, 1)
    monos = monos_slack(s, 9, 7, 3)
    null = explainer_space(D, y, monos, 9)
    Q = random_element(monos, null, rng)
    bad0 = sum(1 for P in flats if any(on_jet(Q, P)))
    bad1 = sum(1 for P in flats if any(on_jet(Q, P, 1)))
    R0 = {(x, aa): v for (x, aa, cc), v in Q.items() if cc == 1}
    R2 = {(x, aa): v for (x, aa, cc), v in Q.items() if cc == 3}
    lhs, rhs = bmul(R0, bpow(a, 2)), bmul(R2, bpow(c, 2))
    prop = not any(lhs.get(key, 0) ^ rhs.get(key, 0) for key in set(lhs) | set(rhs))
    print(f"   (iii) slack support (0,1,0,1), m = 9: |S| = {len(monos)}, n R(9, 3) = {n * R(9, 3)}, space of dimension {len(null)}; random Q: flats with Q != 0: {bad0}, "
          f"with dQ/dY1 != 0: {bad1}; dQ/dY1 = Q_1 + Q_3 Y1^2 with Q_1, Q_3 nonzero: {bool(R0)}, {bool(R2)}; Q_1 a^2 = Q_3 c^2: {prop}")
    print("   (ii) rate 1/2, n = 16, Delta = 7, planted polynomial with A agreements, and a random word")
    for (A, q, m) in ((12, 2, 6), (11, 2, 9)):
        Dc = 7
        Dm = lib.subspace_domain(4, seed=5)
        monos = monos_even(q, 1, m, A, Dc)
        for word in ("planted", "random"):
            if word == "planted":
                P = [rng.randrange(256) for _ in range(Dc + 1)]
                yy = [lib.peval(P, al) for al in Dm]
                for pos in rng.sample(range(16), 16 - A):
                    yy[pos] ^= rng.randrange(1, 256)
            else:
                P = None
                yy = [rng.randrange(256) for _ in Dm]
            null = explainer_space(Dm, yy, monos, m)
            line = f"       A = {A}, even support q = {q}, m = {m}: |S| = {len(monos)}, n rho = {16 * rho(q, 1, m)}, {word} word: space of dimension {len(null)}"
            if null:
                Rr = random_element(monos, null, rng)
                Pr = [rng.randrange(256) for _ in range(Dc + 1)]
                line += f"; R on the jet of a random polynomial: {'!= 0' if any(on_jet(Rr, Pr)) else '= 0'}"
                if P:
                    line += f"; on the jet of the planted member: {'!= 0 (VIOLATION)' if any(on_jet(Rr, P)) else '= 0'}"
            print(line)
            sys.stdout.flush()


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "C", "D"]
    for wh in which:
        {"A": part_A, "B": part_B, "C": part_C, "D": part_D}[wh]()
