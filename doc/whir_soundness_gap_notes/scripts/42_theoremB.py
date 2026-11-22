#!/usr/bin/env python3
"""Note 42 (referee of note 36): an independent evaluation of the final inequality of Theorem B.

Theorem B (note 36, section 4.2), for n uniformly random distinct points of a set of m elements of a field
of q elements, polynomials of degree < k, h = k - 1, lam = log2(m / h), t >= 2 members, list size M,
tilts sD, sC in (0, 1), alpha = (1 - sD) log2 q, beta = (1 - sC) lam:

  log2 Pr[some word has M polynomials at agreement A]
      <= (t-1) k log2 q - n psi_cc(A/n) + C(t,2) n (alpha (t-1) + beta) / M
         + n log2((1 + q^-sD)^(t-1) + C(t-1,2) 2^(-sC lam)) + n^2 / ((m - n) ln 2),

  psi(d) = alpha (t-1) d^2 + beta (1 - d) Pr[Bin(t-1, d) >= 2],  psi_cc its convex envelope on [0, 1].

Nothing is shared with scripts/36_bounds.py. Differences of method:
  * the convex envelope is exact: psi'' has the sign pattern (+, -, +) at most, so the envelope is psi
    outside one interval [a, b] and the chord on it; (a, b) is found by bisection on the common slope
    (no grid, no curvature correction);
  * the tilts are optimized continuously (coordinate search from a grid), t over all integers in a range;
  * the reported bound is re-evaluated in 60-digit decimal arithmetic with a supporting-line certificate
    for the envelope (any line below psi gives a valid lower bound of psi_cc), the minimum of
    psi - line being located by the same convexity structure and cross-checked on a dense scan.

Usage: python3 42_theoremB.py [quick|level0|later|listsize]
  quick: level 0 and the sizes n = 2^25; level0: level 0 and all sizes (3 minutes);
  later [i ...]: the later levels only, all or those listed (20 minutes); listsize: level 0 with list bounds 2^32 to 2^64;
  no argument: level 0, all sizes and the later levels.
"""
import math
import sys
from decimal import Decimal, getcontext

LN2 = math.log(2.0)
LOG2_M = 64  # list size 2^64
TARGET = -100.0

# ------------------------------------------------------------------ psi and its envelope (floats)


def Bge2(T, d):
    """Pr[Bin(T, d) >= 2] = 1 - (1-d)^(T-1) (1 + (T-1) d)."""
    if T < 2 or d <= 0.0:
        return 0.0
    if d >= 1.0:
        return 1.0
    return -math.expm1((T - 1) * math.log1p(-d) + math.log1p((T - 1) * d))


class Psi:
    def __init__(self, t, alpha, beta):
        self.T = T = t - 1
        self.al, self.be = alpha, beta
        self.seg = None  # (a, b): the envelope is the chord on [a, b]
        if T >= 2 and beta > 0:
            dstar = min(1.0, (2 * T - 1) / ((T + 1) * (T - 1)))
            if self.d2(dstar) < 0:
                d1 = self._bis(self.d2, 0.0, dstar)  # d2 > 0 at 0
                d2 = self._bis(lambda x: -self.d2(x), dstar, 1.0) if self.d2(1.0) > 0 else 1.0
                self.seg = self._bitangent(d1, d2)

    def f(self, d):
        return self.al * self.T * d * d + self.be * (1 - d) * Bge2(self.T, d)

    def d1f(self, d):
        T = self.T
        if d >= 1.0:
            return 2 * self.al * T - self.be * (1.0 if T >= 2 else 0.0)
        return 2 * self.al * T * d + self.be * (-Bge2(T, d) + T * (T - 1) * d * (1 - d) ** (T - 1))

    def d2(self, d):
        T = self.T
        if T < 2:
            return 2 * self.al * T
        w = (1 - d) ** (T - 2) if d < 1.0 else (1.0 if T == 2 else 0.0)
        return 2 * self.al * T + self.be * T * (T - 1) * w * (1 - (T + 1) * d)

    @staticmethod
    def _bis(g, lo, hi, it=80):
        """root of g on [lo, hi], g(lo) > 0 > g(hi)."""
        for _ in range(it):
            mid = 0.5 * (lo + hi)
            if g(mid) > 0:
                lo = mid
            else:
                hi = mid
        return 0.5 * (lo + hi)

    def _argmin(self, s, lo, hi):
        """argmin of psi(d) - s d on [lo, hi], where psi is convex."""
        if self.d1f(lo) >= s:
            return lo
        if self.d1f(hi) <= s:
            return hi
        return self._bis(lambda x: s - self.d1f(x), lo, hi, 70)

    def _bitangent(self, d1, d2):
        slo = min(self.d1f(0.0), self.d1f(d2)) - 1.0
        shi = max(self.d1f(d1), self.d1f(1.0)) + 1.0
        for _ in range(70):
            s = 0.5 * (slo + shi)
            a = self._argmin(s, 0.0, d1)
            b = self._argmin(s, d2, 1.0)
            if (self.f(b) - s * b) - (self.f(a) - s * a) > 0:
                slo = s
            else:
                shi = s
        s = 0.5 * (slo + shi)
        return self._argmin(s, 0.0, d1), self._argmin(s, d2, 1.0)

    def cc(self, tau):
        if self.seg is None:
            return self.f(tau)
        a, b = self.seg
        if tau <= a or tau >= b:
            return self.f(tau)
        return self.f(a) + (self.f(b) - self.f(a)) * (tau - a) / (b - a)

    def line(self, tau):
        """slope and intercept at tau of a supporting line of the envelope."""
        if self.seg is not None and self.seg[0] < tau < self.seg[1]:
            a, b = self.seg
            s = (self.f(b) - self.f(a)) / (b - a)
        else:
            s = self.d1f(tau)
        return s


# ------------------------------------------------------------------ the bound


class Case:
    """One code: n points, dimension k, field bits logq, sampling set of 2^log2m points.

    kcost: dimension counted in units of logq bits (k, or k/2 for Theorem B');
    lam:   log2(m / h) with h the largest number of sampled points at which two members agree."""

    def __init__(self, name, n, k, logq, log2m, kcost=None, lam=None, log2m_distinct=None):
        self.name, self.n, self.k, self.logq = name, n, k, logq
        self.kcost = k if kcost is None else kcost
        self.lam = (log2m - math.log2(k - 1)) if lam is None else lam
        lm = log2m if log2m_distinct is None else log2m_distinct
        self.distinct = n * n / ((2.0 ** lm - n) * LN2)

    def bound(self, tau, t, sD, sC):
        n = self.n
        A = math.ceil(tau * n)
        ta = A / n
        al, be = (1 - sD) * self.logq, (1 - sC) * self.lam
        p = Psi(t, al, be)
        corr = math.comb(t, 2) * n * (al * (t - 1) + be) / 2.0 ** LOG2_M
        zD = (t - 1) * math.log2(1.0 + 2.0 ** (-sD * self.logq))
        zC = math.log2(math.comb(t - 1, 2)) - sC * self.lam if t >= 3 else -math.inf
        mx = max(zD, zC)
        lZ = mx + math.log2(2.0 ** (zD - mx) + (2.0 ** (zC - mx) if zC > -math.inf else 0.0))
        return (t - 1) * self.kcost * self.logq - n * p.cc(ta) + corr + n * lZ + self.distinct

    def best_tilt(self, tau, t, start=None):
        """minimize over (sD, sC) by coordinate search in log scale."""
        f = lambda u: self.bound(tau, t, u[0], u[1])
        if start is None:
            best = (math.inf, None)
            for sD in (0.004, 0.01, 0.02, 0.04, 0.08, 0.15, 0.3):
                for sC in (0.01, 0.03, 0.07, 0.15, 0.3, 0.6):
                    v = f((sD, sC))
                    if v < best[0]:
                        best = (v, (sD, sC))
            cur = list(best[1])
        else:
            cur = list(start)
        val = f(cur)
        step = 0.5
        for _ in range(24):
            improved = False
            for i in (0, 1):
                for mult in (math.exp(step), math.exp(-step)):
                    cand = list(cur)
                    cand[i] = min(0.999, max(1e-5, cur[i] * mult))
                    v = f(cand)
                    if v < val - 1e-9:
                        cur, val, improved = cand, v, True
            if not improved:
                step *= 0.5
                if step < 2e-4:
                    break
        return val, tuple(cur)

    def coarse(self, tau, t, small=False):
        best = (math.inf, None)
        for sD in ((0.01, 0.04, 0.1, 0.2, 0.35) if small else (0.004, 0.01, 0.02, 0.04, 0.08, 0.15, 0.3)):
            for sC in ((0.02, 0.07, 0.15, 0.3, 0.5) if small else (0.01, 0.03, 0.07, 0.15, 0.3, 0.6)):
                v = self.bound(tau, t, sD, sC)
                if v < best[0]:
                    best = (v, (sD, sC))
        return best

    def best(self, tau, ts):
        """coarse tilt grid for every t, then a continuous tilt search for the three best t."""
        cand = sorted((self.coarse(tau, t, len(ts) > 30) + (t,) for t in ts), key=lambda r: r[0])[:3]
        best = (math.inf, None, None)
        for v0, u0, t in cand:
            v, u = self.best_tilt(tau, t, start=u0)
            if v < best[0]:
                best = (v, t, u)
        return best

    def threshold(self, ts, lo, hi, steps=40):
        """smallest tau in [lo, hi] at which the best bound is <= TARGET.

        Alternates a re-optimization of (t, sD, sC) at the current tau (cold over all t in the first two
        rounds, and always warm from the current tilts over the nearby t) with a bisection in tau at fixed
        parameters, until the bisection no longer moves by one unit of A = ceil(tau n). The bound is then
        checked to fail just below (run())."""
        v, t, u = self.best(hi, ts)
        if v > TARGET:
            return None
        cur = hi
        for it in range(200):
            a, b = lo, cur
            for _ in range(steps):
                mid = 0.5 * (a + b)
                if self.bound(mid, t, *u) <= TARGET:
                    b = mid
                else:
                    a = mid
            done = cur - b < 0.5 / self.n
            cur = b
            if done and it > 0:
                break
            bv, bt, bu = self.bound(cur, t, *u), t, u
            for tt in window(t, ts):
                vv, uu = self.best_tilt(cur, tt, start=u)
                if vv < bv:
                    bv, bt, bu = vv, tt, uu
            if it < 2:
                v2, t2, u2 = self.best(cur, ts)
                if v2 < bv:
                    bv, bt, bu = v2, t2, u2
            t, u = bt, bu
        return cur, t, u


def window(t, ts):
    i = ts.index(t)
    return ts[max(0, i - 6): i + 7]


def neighbours(t, ts):
    i = ts.index(t)
    return ts[max(0, i - 3): i + 4]


def queries(tau):
    return math.ceil(108.0 / math.log2(1.0 / tau))


# ------------------------------------------------------------------ 60-digit certificate

getcontext().prec = 60
D = Decimal
DLN2 = D(2).ln()


def dlog2(x):
    return x.ln() / DLN2


def certify(case, tau, t, sD, sC, log2m_exact=None):
    """Upper bound of the Theorem B expression in 60-digit arithmetic, with a certified lower bound of the
    envelope: psi_cc(tau) >= L(tau) + min_d (psi(d) - L(d)) for the line L of slope s through (tau, .)."""
    n, T = case.n, t - 1
    A = math.ceil(tau * n)
    ta = D(A) / D(n)
    sDd, sCd = D(repr(sD)), D(repr(sC))
    logq = D(case.logq)
    lam = D(repr(case.lam)) - D("1e-12")  # lam rounded down: beta smaller, pattern term larger
    al, be = (1 - sDd) * logq, (1 - sCd) * lam

    def psi(d):
        d = D(d)
        if T < 2:
            return al * T * d * d
        Bq = 1 - (1 - d) ** (T - 1) * (1 + (T - 1) * d)
        return al * T * d * d + be * (1 - d) * Bq

    def dpsi(d):
        d = D(d)
        if T < 2:
            return 2 * al * T * d
        Bq = 1 - (1 - d) ** (T - 1) * (1 + (T - 1) * d)
        return 2 * al * T * d + be * (-Bq + T * (T - 1) * d * (1 - d) ** (T - 1))

    p = Psi(t, float(al), float(be))
    s = D(repr(p.line(float(ta))))
    h = lambda d: psi(d) - s * (D(d) - ta)
    # candidates for the minimum of h: endpoints, the stationary points in the two convex regions, tau
    cands = [D(0), D(1), ta]
    if p.seg is not None:
        cands += [D(repr(p.seg[0])), D(repr(p.seg[1]))]
    # refine each candidate by a few Newton-free bisection steps on h' around it
    refined = []
    for c in cands:
        lo, hi = max(D(0), c - D("1e-6")), min(D(1), c + D("1e-6"))
        if dpsi(lo) - s < 0 < dpsi(hi) - s:
            for _ in range(120):
                mid = (lo + hi) / 2
                if dpsi(mid) - s < 0:
                    lo = mid
                else:
                    hi = mid
            refined.append((lo + hi) / 2)
    hmin = min(h(c) for c in cands + refined)
    # dense scan as a cross-check of the structure argument (floats are enough here)
    scan = min(p.f(x) - float(s) * (x - float(ta)) for x in ([i / 20000 for i in range(20001)] + [10 ** (-12 * i / 20000) for i in range(20001)]))
    slack_scan = scan - float(hmin)
    env_lower = hmin  # h(tau) = psi(tau) >= hmin, and L(tau) + min(psi - L) = hmin
    corr = D(math.comb(t, 2)) * n * (al * T + be) / D(2) ** LOG2_M
    xq = (D(2) ** (-sDd * logq))
    zc = D(math.comb(T, 2)) * D(2) ** (-sCd * lam) if T >= 2 else D(0)
    lZ = dlog2((1 + xq) ** T + zc)
    lm = D(2) ** (log2m_exact if log2m_exact is not None else 64)
    distinct = D(n) * n / ((lm - n) * DLN2)
    val = D(T) * D(repr(case.kcost)) * logq - n * env_lower + corr + n * lZ + distinct
    return float(val), slack_scan


# ------------------------------------------------------------------ tables


def run(case, ts, lo, hi, note36=None, log2m_exact=None, john=None):
    r = case.threshold(ts, lo, hi)
    john = math.sqrt((case.k - 1) / case.n) if john is None else john
    if r is None:
        print(f"| {case.name} | {john:.4f} ({queries(john)}) | none below {hi:.4f} | | | {note36 or ''} |", flush=True)
        return None
    tau, t, u = r
    # report tau rounded up to 5 decimals (6 for the short codes) and certify there; then show that one
    # step lower fails for every t
    unit = 1e-5 if case.n >= 2 ** 22 else 1e-6
    tau5 = math.ceil(tau / unit - 1e-6) * unit
    v, t5, u5 = case.best(tau5, window(t, ts))
    v0 = case.bound(tau5, t, *u)
    if v0 < v:
        v, t5, u5 = v0, t, u
    cert, slack = certify(case, tau5, t5, u5[0], u5[1], log2m_exact)
    below = tau5 - 2 * unit
    vb, tb = math.inf, None
    for tt in window(t5, ts):  # warm start from the parameters of the threshold, for every nearby t
        vv, _ = case.best_tilt(below, tt, start=u5)
        if vv < vb:
            vb, tb = vv, tt
    print(f"| {case.name} | {john:.4f} ({queries(john)}) | {tau5:.6f} ({queries(tau5)}) t={t5} sD={u5[0]:.4f} sC={u5[1]:.4f} | "
          f"float {v:.1f}, certified {cert:.1f} (scan slack {slack:.1e}) | at {below:.6f}: best found {vb:.0f} (t={tb}) | {note36 or ''} |", flush=True)
    return tau5


def main():
    quick = len(sys.argv) > 1 and sys.argv[1] == "quick"
    later = len(sys.argv) > 1 and sys.argv[1] == "later"
    print("Theorem B of note 36, independent implementation. M = 2^64, target 2^-100.")
    if later:
        return later_levels()
    if len(sys.argv) > 1 and sys.argv[1] == "listsize":
        return list_size()
    print("columns: case | Johnson (queries) | threshold tau (queries), parameters | log2 bound at the threshold | the best bound two units of the last digit below | note 36")
    ts0 = list(range(2, 25))
    print("\n== level 0, k = 2^24 + 6, points in K (q = m = 2^64) ==")
    n36 = {1: "0.6844 (198) t=4", 2: "0.4622 (98) t=5", 3: "0.3079 (64) t=7", 4: "0.2007 (47) t=10"}
    for R in (1, 2, 3, 4):
        n, k = 2 ** (24 + R), 2 ** 24 + 6
        run(Case(f"rate 2^-{R}, n = 2^{24+R}", n, k, 64, 64), ts0, k / n, math.sqrt(k / n), n36[R])
    print("\n== level 0, k = 2^24 + 6, points in E, code over E (q = m = 2^128) ==")
    n36 = {1: "0.6654 (184) t=4", 2: "0.4368 (91) t=5", 3: "0.2803 (59) t=8", 4: "0.1742 (43) t=12"}
    for R in (1, 2, 3, 4):
        n, k = 2 ** (24 + R), 2 ** 24 + 6
        run(Case(f"rate 2^-{R}, n = 2^{24+R}", n, k, 128, 128), ts0, k / n, math.sqrt(k / n), n36[R], 128)
    print("\n== level 0, Theorem B': polynomials over K, points of E minus K (one per conjugate pair) ==")
    n36 = {1: "0.4368 (91) t=5", 2: "0.2803 (59) t=8", 3: "0.1742 (43) t=12", 4: "0.1043 (34) t=16"}
    for R in (1, 2, 3, 4):
        n, k = 2 ** (24 + R), 2 ** 24 + 6
        lam = math.log2((2.0 ** 128 - 2.0 ** 64) / (k - 1))
        c = Case(f"rate 2^-{R}, n = 2^{24+R}", n, k, 128, 128, kcost=k / 2.0, lam=lam, log2m_distinct=127)
        run(c, ts0, k / (2 * n), math.sqrt(k / (2.0 * n)), n36[R], 127, john=math.sqrt((k - 1) / (2.0 * n)))
    print("\n== all sizes: n = 2^25..2^28 times the four rates, k = rho n + 6, points in K ==")
    for ln in (25, 26, 27, 28):
        for R in (1, 2, 3, 4):
            n = 2 ** ln
            k = n // 2 ** R + 6
            run(Case(f"n = 2^{ln}, rate 2^-{R}", n, k, 64, 64), ts0, k / n, math.sqrt(k / n))
        if quick:
            break
    if quick or (len(sys.argv) > 1 and sys.argv[1] == "level0"):
        return
    later_levels()


def list_size():
    """the level-0 thresholds with points in K for smaller list bounds M."""
    global LOG2_M
    print("\n== level 0, points in K: the threshold as a function of the list bound M ==")
    for lm in (64, 48, 40, 36, 32):
        LOG2_M = lm
        out = []
        for R in (1, 2, 3, 4):
            n, k = 2 ** (24 + R), 2 ** 24 + 6
            r = Case("x", n, k, 64, 64).threshold(list(range(2, 16)), k / n, math.sqrt(k / n))
            out.append(f"{r[0]:.5f} (t={r[1]})")
        print(f"M = 2^{lm}: " + ", ".join(out), flush=True)
    LOG2_M = 64


def later_levels():
    print("\n== later levels of the mu = 30, R = 1 ladder: k = 2^(24-4i) + 4, n = 2^(25-i) ==")
    tsL = list(range(2, 41)) + [44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 112, 128, 144, 160, 192, 224, 256, 320, 384, 448, 512, 640, 768, 1024]
    n36K = {1: "0.1946 (46) t=10", 2: "0.0425 (24) t=32", 3: "0.0089 (16) t=80", 4: "0.0020 (13) t=160", 5: "0.0005 (10) t=384"}
    n36E = {1: "0.1714 (43) t=12", 2: "0.0350 (23) t=32", 3: "0.0073 (16) t=80", 4: "0.0016 (12) t=256", 5: "0.0004 (10) t=256"}
    only = [int(x) for x in sys.argv[2:]] or [1, 2, 3, 4, 5]
    for i in only:
        k, n = 2 ** (24 - 4 * i) + 4, 2 ** (25 - i)
        run(Case(f"level {i}, rate 2^-{1+3*i}, points in K", n, k, 64, 64), tsL, k / n, math.sqrt(k / n), n36K[i])
        run(Case(f"level {i}, rate 2^-{1+3*i}, points in E", n, k, 128, 128), tsL, k / n, math.sqrt(k / n), n36E[i], 128)


if __name__ == "__main__":
    main()
