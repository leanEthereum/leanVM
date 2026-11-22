#!/usr/bin/env python3
"""Note 36: explicit list bounds for Reed-Solomon codes on random evaluation points.

Evaluates, with exact constants, the theorems of note 36. All of them bound the probability, over n
uniformly random distinct points of a set of size m, that some word has at least M = 2^64 polynomials
of degree < k agreeing with it on at least ceil(tau n) points.

  Theorem A (rank certificates, after Alrabiah-Guo-Guruswami-Li-Zhang, section 3)
  Theorem B (star counting, after Ferber-Kwan-Sauermann, Theorem 4)
  Theorem B_w (the same on a union of cosets of a fixed subspace of size w, random representatives)

and one heuristic that is NOT a theorem (table T5, regular lists).

Pure standard library. Usage: python3 36_bounds.py [quick]   (about half a minute; quick: a few seconds)
"""
import bisect
import math
import sys

LN2 = math.log(2.0)
LOG2M_LIST = 64  # list bound M = 2^64 in every theorem
TARGET = -100.0  # log2 of the allowed failure probability


def log2sumexp(vals):
    m = max(vals)
    if m == -math.inf:
        return m
    return m + math.log2(sum(2.0 ** (v - m) for v in vals))


# ---------------------------------------------------------------- Theorem A


def log2_Zs(s, lx):
    """log2 of Z_s(x) = 1 + ((1+x)^s - 1 - s x)/x, x = 2^lx: one label per edge of size >= 2, weight x^(|e|-1)."""
    x = 2.0 ** lx
    if x < 1e-6:
        tot = 0.0
        for j in range(2, min(s, 12) + 1):
            tot += math.comb(s, j) * x ** (j - 1)
        return math.log1p(tot) / LN2
    big = s * math.log2(1.0 + x) - lx
    if big > 60:
        return big
    return math.log2(1.0 + ((1.0 + x) ** s - 1.0 - s * x) / x)


def log2_count_hypergraphs(n, s, weight):
    """min over x > 0 of n log2 Z_s(x) - weight log2 x: bounds the number of edge sequences of total weight `weight`."""
    f = lambda lx: n * log2_Zs(s, lx) - weight * lx
    lo, hi = -60.0, 40.0
    for _ in range(200):  # ternary search, f is convex in lx
        a, b = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if f(a) < f(b):
            hi = b
        else:
            lo = a
    return f(0.5 * (lo + hi))


def theorem_A(n, kdim, log2m, tau, t):
    """log2 of the Theorem A bound for t members. None if the deletion budget is empty."""
    a = math.ceil(tau * n)
    if a > n:
        return None
    corr = 1.0 + (t - 1) / 2.0 ** LOG2M_LIST * 1.0000001  # M / (M - t + 1), rounded up
    wstar = math.floor(t * a - n + n * max(0.0, 1.0 - (a / n) * corr) ** t) - 1
    kappa = wstar // (t - 1)
    D = kappa - kdim  # coordinates that may be deleted
    if D < 1:
        return None
    log2p1 = math.log2(kdim - 1) - (log2m + math.log2(1.0 - n / 2.0 ** log2m))  # (k-1)/(m-n), rounded up
    terms = []
    for s in range(3, t + 1):
        Ts = 2 ** s - s - 1
        Ws = (s - 1) * kappa
        lN = log2_count_hypergraphs(n, s, Ws)
        best = math.inf
        cands = {0}  # bank of b indices per type, r faults, Ts*b + r - 1 <= D
        b = 1
        while Ts * b < D:
            cands.add(b)
            b = max(b + 1, int(b * 1.15))
        for b in cands:
            r = D + 1 - Ts * b
            if r < 1:
                continue
            runs = -(-r // (b + 1))
            v = r * math.log2(runs) + r * (math.log2(Ws) + log2p1) - math.lgamma(r + 1) / LN2
            best = min(best, v)
        terms.append(lN + best)
    return log2sumexp(terms)


def best_A(n, kdim, log2m, tau, tmax=14):
    best, arg = math.inf, None
    for t in range(3, tmax + 1):
        v = theorem_A(n, kdim, log2m, tau, t)
        if v is not None and v < best:
            best, arg = v, t
    return best, arg


# ---------------------------------------------------------------- Theorem B and B_w

GRID = 1000
SD = (0.006, 0.012, 0.025, 0.045, 0.08, 0.13, 0.2)
SC = (0.015, 0.03, 0.06, 0.1, 0.16, 0.26, 0.4, 0.6)
TS_B = [2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128, 160, 200, 256, 384, 512, 768, 1024]
_TABS = {}


def star_tables(t):
    """On the grid: d^2, (1-d) Pr[Bin(t-1,d) >= 2] (C-eligible), d (1 - (1-d)^(t-1)) (D-eligible)."""
    if t in _TABS:
        return _TABS[t]
    T = t - 1
    xs = [i / GRID for i in range(GRID + 1)]
    dd = [x * x for x in xs]
    cc, de = [], []
    for x in xs:
        if x >= 1.0:
            cc.append(0.0)
            de.append(1.0)
        else:
            cc.append((1 - x) * (1.0 - (1 - x) ** T - T * x * (1 - x) ** (T - 1)))
            de.append(x * (1.0 - (1 - x) ** T))
    _TABS[t] = (xs, dd, cc, de)
    return _TABS[t]


def lower_hull(xs, ys):
    hull = []
    for p in zip(xs, ys):
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (x2 - x1) * (p[1] - y1) - (y2 - y1) * (p[0] - x1) <= 0:
                hull.pop()
            else:
                break
        hull.append(p)
    return [p[0] for p in hull], [p[1] for p in hull]


class Star:
    """Theorem B (w = 1) or B_w for fixed (logq, lam, w): the convex envelopes for every t and tilt, then values.

    logq: bits per dimension of a member (64 or 128).
    lam:  log2(m / h), m the size of the sampling set, h the largest number of its points on which two
          distinct members agree.
    """

    def __init__(self, logq, lam, w=1, ts=TS_B):
        self.logq, self.lam, self.w, self.ts = logq, lam, w, ts
        self.lamw = lam - math.log2(w)
        self.items = {}
        for t in ts:
            xs, dd, cc, de = star_tables(t)
            lst = []
            for sD in SD:
                al = (1 - sD) * logq
                zD = (t - 1) * w * math.log2(1.0 + 2.0 ** (-sD * logq))
                if zD > 40:
                    continue
                for sC in SC:
                    be = (1 - sC) * self.lamw
                    if w == 1:
                        ys = [al * (t - 1) * u + be * v for u, v in zip(dd, cc)]
                    else:
                        ys = [al * (t - 1) * u + be * (v / w - x) for u, v, x in zip(dd, cc, de)]
                    hx, hy = lower_hull(xs, ys)
                    # the hull of the grid points is above the convex envelope by at most max|psi''| h^2 / 8
                    curv = max(abs(ys[i - 1] - 2 * ys[i] + ys[i + 1]) for i in range(1, GRID)) / 8.0
                    lZ = math.log2(2.0 ** zD + w * math.comb(t - 1, 2) * 2.0 ** (-sC * self.lamw))
                    lst.append((al, be, hx, hy, curv, lZ))
            self.items[t] = lst

    def value(self, n, kcost, log2m, tau, t):
        """log2 of the bound for t members; kcost is the dimension in units of logq bits."""
        a = math.ceil(tau * n)
        ta = a / n
        ncos = n // self.w
        distinct = 2.0 * ncos * ncos / 2.0 ** (log2m - math.log2(self.w)) / LN2
        best = math.inf
        for al, be, hx, hy, curv, lZ in self.items[t]:
            j = bisect.bisect_right(hx, ta) - 1
            j = min(max(j, 0), len(hx) - 2)
            psi = hy[j] + (hy[j + 1] - hy[j]) * (ta - hx[j]) / (hx[j + 1] - hx[j]) - curv
            # sampling the t members without replacement from M = 2^64 instead of independently
            err = math.comb(t, 2) / 2.0 ** LOG2M_LIST * n * (al * (t - 1) * self.w + be)
            val = (t - 1) * kcost * self.logq - (n * psi - err) + ncos * lZ + distinct + 1.0
            best = min(best, val)
        return best

    def best(self, n, kcost, log2m, tau):
        best, arg = math.inf, None
        for t in self.ts:
            v = self.value(n, kcost, log2m, tau, t)
            if v < best:
                best, arg = v, t
        return best, arg


# ---------------------------------------------------------------- searches


def threshold(pred, lo, hi, steps=15):
    """Smallest tau in [lo, hi] with pred(tau), by bisection (the bounds are monotone in tau on these ranges)."""
    if not pred(hi):
        return None
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        if pred(mid):
            hi = mid
        else:
            lo = mid
    return hi


def queries(tau):
    return math.ceil(108.0 / math.log2(1.0 / tau))


def row(name, n, k, ell, log2m, logq, e_points_k_polys=False, do_A=True, tmaxA=14):
    kdim = k + ell
    rho = kdim / n
    john = math.sqrt((kdim - 1) / n)
    tauA = tA = None
    if do_A and not e_points_k_polys:
        fA = lambda tau: best_A(n, kdim, log2m, tau, tmaxA)[0] <= TARGET
        tauA = threshold(fA, rho, min(0.999, 1.6 * john))
        tA = best_A(n, kdim, log2m, tauA, tmaxA)[1] if tauA else None
    if e_points_k_polys:
        # polynomials over K at points of E minus K, one point per conjugate pair
        kcost, lam = kdim / 2.0, math.log2((2.0 ** 128 - 2.0 ** 64) / (kdim - 1))
        john = math.sqrt((kdim - 1) / (2.0 * n))
        lo = rho / 2
    else:
        kcost, lam = float(kdim), log2m - math.log2(kdim - 1)
        lo = rho
    st = Star(logq, lam)
    fB = lambda tau: st.best(n, kcost, log2m, tau)[0] <= TARGET
    tauB = threshold(fB, lo, min(0.999, 1.6 * john))
    tB = st.best(n, kcost, log2m, tauB)[1] if tauB else None
    return dict(name=name, john=john, tauA=tauA, tA=tA, tauB=tauB, tB=tB)


def fmt(r):
    def one(tau, t):
        if tau is None:
            return "none"
        return f"{tau:.4f} (t={t}, q={queries(tau)})"

    return f"| {r['name']} | {r['john']:.4f} ({queries(r['john'])}) | {one(r['tauA'], r['tA'])} | {one(r['tauB'], r['tB'])} |"


# ---------------------------------------------------------------- heuristic of section 6 (not a theorem)


def regular_exponent(rho, tau, logq, lam, t, r):
    """HEURISTIC: exponent per coordinate of the sequential multi-parent count on a regular list
    (every coordinate in a tau fraction of the members, independently)."""
    q1 = 1.0 - tau
    u = lambda j: 1.0 - q1 ** j
    B = lambda j: 1.0 - q1 ** j - j * tau * q1 ** (j - 1)
    cost = 0.0
    for j in range(2, t + 1):
        c = tau * u(j - 1) if j <= r else tau * B(j - 1)
        cost += max(0.0, rho - c) * logq
    gain = lam * (B(t) - B(r))
    p1 = q1 ** t + t * tau * q1 ** (t - 1)
    ent = -p1 * math.log2(p1)
    lt, l1 = math.log2(tau), math.log2(q1)
    for j in range(2, t + 1):
        lpj = j * lt + (t - j) * l1
        lc = (math.lgamma(t + 1) - math.lgamma(j + 1) - math.lgamma(t - j + 1)) / LN2
        if lc + lpj > -200:
            ent -= 2.0 ** (lc + lpj) * lpj
    return cost - gain + ent


def regular_threshold(rho, logq, lam, john):
    ts = list(range(3, 33)) + [40, 48, 64, 80, 96, 128, 160, 200, 256, 320, 400]

    def ok(tau):
        for t in ts:
            for r in list(range(1, min(t, 17))) + [r0 for r0 in (20, 24, 32, 48, 64) if r0 < t]:
                if regular_exponent(rho, tau, logq, lam, t, r) < 0:
                    return True
        return False

    return threshold(ok, rho, john, 13)


# ---------------------------------------------------------------- tables


def main():
    quick = len(sys.argv) > 1 and sys.argv[1] == "quick"
    print("list size M = 2^64, failure probability 2^-100, analysis degree < k + ell")
    print("columns: Johnson agreement (queries) | Theorem A: tau (members t, queries) | Theorem B: tau (t, queries)")
    print("queries = ceil(108 / log2(1/tau))")

    print("\n== T1. level 0, mu = 30: k = 2^24, K-valued lanes, ell = 6 ==")
    for R in (1, 2, 3, 4):
        n, k = 2 ** (24 + R), 2 ** 24
        print(fmt(row(f"rate 2^-{R}, points in K, sampled from 2^64", n, k, 6, 64, 64)), flush=True)
        print(fmt(row(f"rate 2^-{R}, points in E, code over E", n, k, 6, 128, 128)), flush=True)
        print(fmt(row(f"rate 2^-{R}, points in E minus K, polynomials over K", n, k, 6, 128, 128, e_points_k_polys=True)), flush=True)
        if quick:
            break

    print("\n== T2. later levels of the mu = 30, R = 1 ladder: k = 2^(24-4i), n = 2^(25-i), E-valued lanes, ell = 4 ==")
    for i in range(1, 6):
        k, n = 2 ** (24 - 4 * i), 2 ** (25 - i)
        print(fmt(row(f"level {i}, rate 2^-{1+3*i}, points in K", n, k, 4, 64, 64)), flush=True)
        print(fmt(row(f"level {i}, rate 2^-{1+3*i}, points in E", n, k, 4, 128, 128)), flush=True)
        if quick:
            break

    print("\n== T3. level 0, sampling set of size 2^b inside a field of 2^b elements ==")
    for R in (1, 2, 3, 4):
        n, k = 2 ** (24 + R), 2 ** 24
        for lb in (48, 80, 96, 192, 256):
            print(fmt(row(f"rate 2^-{R}, b = {lb}", n, k, 6, lb, lb)), flush=True)
        if quick:
            break

    print("\n== T4. Theorem A at level 0 with points in K: log2 of the bound at the Johnson agreement ==")
    for R in (1, 2, 3, 4):
        n, k = 2 ** (24 + R), 2 ** 24
        kdim = k + 6
        john = math.sqrt((kdim - 1) / n)
        vA, tA = best_A(n, kdim, 64, john, 14)
        print(f"rate 2^-{R}: {vA / n:+.4f} n bits (best t = {tA}); a negative value is needed", flush=True)
        if quick:
            break

    print("\n== T6. Theorem B_w: union of n/w cosets of a fixed subspace of size w, random representatives in K ==")
    ws = (2, 4, 16, 64)
    print("smallest tau (queries) for w = " + ", ".join(map(str, ws)))
    cases = [(f"level 0 rate 2^-{R}", 2 ** (24 + R), 2 ** 24, 6) for R in (1, 2, 3, 4)]
    cases += [(f"level {i} rate 2^-{1+3*i}", 2 ** (25 - i), 2 ** (24 - 4 * i), 4) for i in range(1, 6)]
    stars = {}
    for name, n, k, ell in cases:
        kdim = k + ell
        john = math.sqrt((kdim - 1) / n)
        lam = 64 - math.log2(kdim - 1)
        out = []
        for w in ws:
            if w > k:
                out.append("-")
                continue
            key = (round(lam, 6), w)
            if key not in stars:
                stars[key] = Star(64, lam, w)
            st = stars[key]
            f = lambda tau: st.best(n, float(kdim), 64, tau)[0] <= TARGET
            tau = threshold(f, kdim / n, john, 13)
            out.append("none" if tau is None else f"{tau:.4f} ({queries(tau)})")
        print(f"| {name} | {john:.4f} ({queries(john)}) | " + " | ".join(out) + " |", flush=True)
        if quick:
            break

    print("\n== T7. Theorem B, level 0: n random points of a subspace of size 2^c n of K (a longer NTT, then puncture) ==")
    for R in (1, 2, 3, 4):
        n, kdim = 2 ** (24 + R), 2 ** 24 + 6
        john = math.sqrt((kdim - 1) / n)
        out = []
        for c in (1, 2, 4, 8, 12, 16, 24):
            lm = 24 + R + c
            st = Star(64, lm - math.log2(kdim - 1))
            f = lambda tau: st.best(n, float(kdim), lm, tau)[0] <= TARGET
            tau = threshold(f, kdim / n, john, 13)
            out.append(f"c={c}: " + ("none" if tau is None else f"{tau:.4f} ({queries(tau)})"))
        print(f"rate 2^-{R} (Johnson {john:.4f}, {queries(john)}): " + ", ".join(out), flush=True)
        if quick:
            break

    print("\n== T5. HEURISTIC, NOT A THEOREM: regular lists, sequential multi-parent count (note 36 section 6) ==")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        for name, logq, lam in (("K", 64, 40.0), ("E", 128, 104.0)):
            tau = regular_threshold(rho, logq, lam, math.sqrt(rho))
            print(f"level 0 rate 2^-{R}, points in {name}: tau = {tau if tau is None else round(tau, 4)}"
                  + ("" if tau is None else f" ({queries(tau)} queries)"), flush=True)
        if quick:
            break
    for i in range(1, 6):
        if quick:
            break
        rho = 2.0 ** -(1 + 3 * i)
        kap = 24 - 4 * i
        for name, logq in (("K", 64), ("E", 128)):
            tau = regular_threshold(rho, logq, logq - kap, math.sqrt(rho))
            print(f"level {i} rate 2^-{1+3*i}, points in {name}: tau = {tau if tau is None else round(tau, 5)}"
                  + ("" if tau is None else f" ({queries(tau)} queries)"), flush=True)


if __name__ == "__main__":
    main()
