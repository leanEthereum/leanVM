#!/usr/bin/env python3
"""Note 42, part 2: the multi-parent count of note 36 section 6.

Three computations.

1. Theorem C of note 42 (proved there): a two-parent version of Theorem B in which the caps are made
   deterministic by two pigeonhole steps on the list (Lemma R). Members: a centre I_1, a second parent I_2,
   leaves 3..t. After the two steps every remaining member I has |I cap I_1| = c1 and
   |I cap I_2 minus I_1| = c2 with c1 >= A^2/n - 2 and c2 >= (A-c1)^2/(n-A) - 2, the adversary choosing
   anything above. With z = c1 + c2 the labeling has
       units  U = c1 + (t-2) min(z, k),
       roots  R = (z - k)_+  +  x2 Bcc_{t-2}(y2/x2),   x2 = n - 2A + c1,  y2 = A - z,
   and the bound is
       log2 Pr <= (t-1) k log2 q - min_{c1,c2}(alpha U + beta R) + n log2 Z_C + small,
       Z_C = (1+x)^(t-1) + (1+x)^(t-2) - 1 + 2 y (1+x)^(t-3) + C(t-2,2) y,  x = q^-sD, y = 2^(-sC lam).
   The list must have 2^64 (n(n+1))^2 members: 2^180 suffices for n <= 2^28.

2. The heuristic of note 36 (table T5) recomputed, and the same with the better reading of Lemma M
   (every member takes min(z_j, k) units and turns its surplus into roots): regular lists only, no theorem.

3. The stress test of the regularization lemma: product families with a two-point density profile
   (a fraction w of the coordinates has density d1, the rest d2, mean tau, second moment at most rho).
   Every t-tuple of such a family has the same type, so the family defeats the lemma as soon as its
   exponent is larger than the regular one.

Usage: python3 42_multiparent.py [quick]
"""
import math
import sys

LN2 = math.log(2.0)


def Bge2(T, d):
    if T < 2 or d <= 0.0:
        return 0.0
    if d >= 1.0:
        return 1.0
    return -math.expm1((T - 1) * math.log1p(-d) + math.log1p((T - 1) * d))


def dBge2(T, d):
    if T < 2:
        return 0.0
    return T * (T - 1) * d * (1 - d) ** (T - 2) if d < 1 else (2.0 if T == 2 else 0.0)


class Bcc:
    """convex envelope on [0,1] of d -> Pr[Bin(T,d) >= 2]: B on [0, a], then the chord to (1, 1)."""

    def __init__(self, T):
        self.T = T
        self.a = 1.0
        if T >= 3:
            lo, hi = 0.0, 1.0 / (T - 1)
            F = lambda a: dBge2(T, a) * (1 - a) - (1 - Bge2(T, a))
            if F(hi) > 0:
                for _ in range(80):
                    mid = 0.5 * (lo + hi)
                    if F(mid) > 0:
                        hi = mid
                    else:
                        lo = mid
                self.a = 0.5 * (lo + hi)

    def __call__(self, d):
        if self.T < 2:
            return 0.0
        if d <= self.a:
            return Bge2(self.T, d)
        fa = Bge2(self.T, self.a)
        return fa + (1 - fa) * (d - self.a) / (1 - self.a)


def queries(tau):
    return math.ceil(108.0 / math.log2(1.0 / tau))


# ------------------------------------------------------------------ 1. Theorem C


def hull_points(tau, rho, hbar, t, eps, G1=160, G2=240):
    """lower-left convex hull of the points (U, R)/n over the adversary's choices (c1, c2)."""
    T = t - 2
    bcc = Bcc(T)
    pts = []
    c1lo, c1hi = max(0.0, tau * tau - eps, 2 * tau - 1), hbar
    if c1lo > c1hi:
        c1lo = c1hi
    x1 = 1 - tau
    for i in range(G1 + 1):
        c1 = c1lo + (c1hi - c1lo) * i / G1
        y1 = tau - c1
        c2lo = max(0.0, y1 * y1 / x1 - eps)
        c2hi = min(y1, hbar)
        if c2lo > c2hi:
            c2lo = c2hi
        x2 = x1 - y1
        special = [rho - c1]  # the kink z = k
        if x2 > 0:
            special.append(y1 - bcc.a * x2)  # the kink of the envelope
        cands = [c2lo + (c2hi - c2lo) * j / G2 for j in range(G2 + 1)] + [s for s in special if c2lo <= s <= c2hi]
        for c2 in cands:
            z = c1 + c2
            y2 = y1 - c2
            U = c1 + (t - 2) * min(z, rho)
            R = max(z - rho, 0.0) + (x2 * bcc(min(1.0, max(0.0, y2 / x2))) if x2 > 1e-15 else 0.0)
            pts.append((U, R))
    pts.sort()
    # keep the points minimizing a U + b R for some a, b >= 0: lower-left hull
    hull = []
    for p in pts:
        if hull and p[1] >= hull[-1][1]:
            continue  # dominated
        while len(hull) >= 2:
            (u1, r1), (u2, r2) = hull[-2], hull[-1]
            if (u2 - u1) * (p[1] - r1) - (r2 - r1) * (p[0] - u1) <= 0:
                hull.pop()
            else:
                break
        hull.append(p)
    return hull


class TheoremC:
    def __init__(self, n, k, logq, log2m):
        self.n, self.k, self.logq = n, k, logq
        self.lam = log2m - math.log2(k - 1)
        self.rho, self.hbar = k / n, (k - 1) / n
        self.distinct = n * n / ((2.0 ** log2m - n) * LN2)
        self.cache = {}

    def hull(self, tau, t, fine=False):
        key = (tau, t, fine)
        if key not in self.cache:
            g = (640, 960) if fine else (160, 240)
            self.cache[key] = hull_points(tau, self.rho, self.hbar, t, 2.5 / self.n, *g)
        return self.cache[key]

    def bound(self, tau, t, sD, sC, fine=False):
        n = self.n
        ta = math.ceil(tau * n) / n
        al, be = (1 - sD) * self.logq, (1 - sC) * self.lam
        psi = min(al * U + be * R for U, R in self.hull(ta, t, fine))
        x, y = 2.0 ** (-sD * self.logq), 2.0 ** (-sC * self.lam)
        Z = (1 + x) ** (t - 1) + (1 + x) ** (t - 2) - 1 + 2 * y * (1 + x) ** (t - 3) + math.comb(t - 2, 2) * y
        corr = math.comb(t - 2, 2) * n * be / 2.0 ** 64  # Lemma 1 on the 2^64 remaining members
        return (t - 1) * self.k * self.logq - n * psi + n * math.log2(Z) + self.distinct + corr

    def best(self, tau, ts, fine=False):
        best = (math.inf, None, None)
        for t in ts:
            f = lambda u: self.bound(tau, t, u[0], u[1], fine)
            cur, val = None, math.inf
            for sD in (1e-5, 0.004, 0.01, 0.02, 0.04, 0.08, 0.15):
                for sC in (0.003, 0.01, 0.03, 0.07, 0.15, 0.3):
                    v = f((sD, sC))
                    if v < val:
                        cur, val = [sD, sC], v
            step = 0.5
            for _ in range(40):
                improved = False
                for i in (0, 1):
                    for mult in (math.exp(step), math.exp(-step)):
                        cand = list(cur)
                        cand[i] = min(0.999, max(1e-6, cur[i] * mult))
                        v = f(cand)
                        if v < val - 1e-9:
                            cur, val, improved = cand, v, True
                if not improved:
                    step *= 0.5
                    if step < 1e-3:
                        break
            if val < best[0]:
                best = (val, t, tuple(cur))
        return best

    def threshold(self, ts, lo, hi, steps=14):
        if self.best(hi, ts)[0] > -100:
            return None
        for _ in range(steps):
            mid = 0.5 * (lo + hi)
            if self.best(mid, ts)[0] <= -100:
                hi = mid
            else:
                lo = mid
        return hi


# ------------------------------------------------------------------ 2 and 3. heuristics on product families


def H2(p):
    return 0.0 if p <= 0 or p >= 1 else -(p * math.log2(p) + (1 - p) * math.log2(1 - p))


class Profile:
    """atoms [(weight, density)]; all quantities are averages over the coordinates.

    zeta[j]: points of member j in an earlier member; vee[j]: in at least two earlier members;
    ups[j]: points whose second member is j; B[j]: coordinates with at least two of the first j members."""

    def __init__(self, atoms, tmax):
        self.atoms, self.tmax = atoms, tmax
        self.zeta = [0.0] * (tmax + 1)
        self.vee = [0.0] * (tmax + 1)
        self.ups = [0.0] * (tmax + 1)
        self.B = [0.0] * (tmax + 1)
        for w, d in atoms:
            for j in range(1, tmax + 1):
                self.zeta[j] += w * d * (1 - (1 - d) ** (j - 1))
                self.vee[j] += w * d * Bge2(j - 1, d)
                self.ups[j] += w * (j - 1) * d * d * (1 - d) ** (j - 2) if j >= 2 else 0.0
                self.B[j] += w * Bge2(j, d)

    def entropy(self, t):
        """entropy of the label of a coordinate: its member set if it has at least two members, else nothing."""
        p1 = sum(w * ((1 - d) ** t + t * d * (1 - d) ** (t - 1)) for w, d in self.atoms)
        ent = -p1 * math.log2(p1) if p1 > 0 else 0.0
        for j in range(2, t + 1):
            pj = sum(w * d ** j * (1 - d) ** (t - j) for w, d in self.atoms)
            if pj > 1e-300:
                ent -= math.comb(t, j) * pj * math.log2(pj)
        return ent


TS_H = list(range(3, 25)) + [28, 32, 40, 48, 64, 80, 96, 128]


def cost_note36(pr, rho, logq, lam, t, r):
    """Lemma 6.1 of note 36 with parameter r: log2 q sum_j (k - c_j)_+ - lam g, per coordinate."""
    cost = sum(max(0.0, rho - pr.zeta[j]) for j in range(2, r + 1))
    cost += sum(max(0.0, rho - pr.vee[j]) for j in range(r + 1, t + 1))
    return logq * cost - lam * (pr.B[t] - pr.B[r])


def cost_greedy(pr, rho, logq, lam, t):
    """Lemma M with the greedy reading: member j takes min(z_j, k) units and turns min(u_j, z_j - k) points into roots."""
    tot = 0.0
    for j in range(2, t + 1):
        z = pr.zeta[j]
        tot += logq * max(0.0, rho - z) - lam * min(pr.ups[j], max(0.0, z - rho))
    return tot


def best_ex(atoms, rho, logq, lam, greedy, ts=TS_H, want_arg=False):
    """smallest exponent (count plus label entropy) over t and, for the count of note 36, over r."""
    pr = Profile(atoms, max(ts))
    best, arg = math.inf, None
    for t in ts:
        ent = pr.entropy(t)
        if greedy:
            v = cost_greedy(pr, rho, logq, lam, t) + ent
            if v < best:
                best, arg = v, (t, None)
        else:
            for r in range(1, min(t, 12) + 1):
                v = cost_note36(pr, rho, logq, lam, t, r) + ent
                if v < best:
                    best, arg = v, (t, r)
    return (best, arg) if want_arg else best


def regular_threshold(rho, logq, lam, greedy):
    lo, hi = rho, math.sqrt(rho)
    for _ in range(40):
        mid = 0.5 * (lo + hi)
        if best_ex([(1.0, mid)], rho, logq, lam, greedy) < 0:
            hi = mid
        else:
            lo = mid
    return hi


def two_point_profiles(tau, rho, G):
    for i in range(G + 1):
        d1 = tau * i / G  # the low density, in [0, tau]
        for j in range(1, G + 1):
            d2 = tau + (1 - tau) * j / G  # the high density, in (tau, 1]
            w2 = (tau - d1) / (d2 - d1)
            w1 = 1 - w2
            if w2 <= 0 or w1 <= 0 or w1 * d1 * d1 + w2 * d2 * d2 > rho:
                continue
            yield [(w1, d1), (w2, d2)]


def worst_profile(tau, rho, logq, lam, greedy, G=60, ts=TS_H):
    """largest exponent over two-point profiles of mean tau and second moment <= rho."""
    worst = (best_ex([(1.0, tau)], rho, logq, lam, greedy, ts), None)
    for atoms in two_point_profiles(tau, rho, G):
        v = best_ex(atoms, rho, logq, lam, greedy, ts)
        if v > worst[0]:
            worst = (v, atoms)
    return worst


def robust_threshold(rho, logq, lam, greedy, lo, hi, G=30, ts=TS_H):
    for _ in range(14):
        mid = 0.5 * (lo + hi)
        if worst_profile(mid, rho, logq, lam, greedy, G, ts)[0] < 0:
            hi = mid
        else:
            lo = mid
    return hi


def main():
    quick = len(sys.argv) > 1 and sys.argv[1] == "quick"
    print("== 1. Theorem C (two parents, caps made deterministic by two pigeonhole steps), list size 2^180, failure 2^-100 ==")
    print("case | Johnson | Theorem B (42_theoremB.py) | Theorem C: tau (queries), t, tilts, log2 bound on the fine grid")
    thmB = {(1, 64): 0.68391, (2, 64): 0.46214, (3, 64): 0.30757, (4, 64): 0.20037, (1, 128): 0.66482, (2, 128): 0.43679, (3, 128): 0.28014, (4, 128): 0.17390}
    for logq in (64, 128):
        for R in (1, 2, 3, 4):
            n, k = 2 ** (24 + R), 2 ** 24 + 6
            c = TheoremC(n, k, logq, logq)
            ts = list(range(4, 13 if R <= 2 else 20))
            tau = c.threshold(ts, k / n, math.sqrt(k / n))
            if tau is None:
                print(f"rate 2^-{R}, points in {'K' if logq == 64 else 'E'}: none below Johnson", flush=True)
                continue
            tau5 = math.ceil(tau * 1e4) / 1e4
            v, t, u = c.best(tau5, ts)
            vf = c.bound(tau5, t, u[0], u[1], fine=True)
            b = thmB[(R, logq)]
            print(f"rate 2^-{R}, points in {'K' if logq == 64 else 'E'} | {math.sqrt(k/n):.4f} ({queries(math.sqrt(k/n))}) | {b:.4f} ({queries(b)}) | "
                  f"{tau5:.4f} ({queries(tau5)}) t={t} sD={u[0]:.4f} sC={u[1]:.4f} bound {v:.0f}, fine grid {vf:.0f}", flush=True)
            if quick:
                break
        if quick:
            break

    print("\n== 2. heuristics on regular lists (no theorem): smallest tau with a negative exponent ==")
    print("case | note 36 count (table T5 there) | greedy reading of Lemma M")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        for name, logq, lam in (("K", 64, 40.0), ("E", 128, 104.0)):
            a = regular_threshold(rho, logq, lam, False)
            b = regular_threshold(rho, logq, lam, True)
            print(f"level 0 rate 2^-{R}, points in {name}: {a:.4f} ({queries(a)}) | {b:.4f} ({queries(b)})", flush=True)

    print("\n== 3. product families with a two-point density profile against the regular one (points in K) ==")
    print("tau = regular threshold + 0.002, where the regular exponent is negative. Exponent = count + label entropy, per coordinate.")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        logq, lam = 64, 40.0
        ts = [t for t in TS_H if t <= (24 if R <= 2 else 64)]
        for greedy in (False, True):
            name = "greedy" if greedy else "note 36"
            treg = regular_threshold(rho, logq, lam, greedy)
            tau = treg + 0.002
            reg, arg = best_ex([(1.0, tau)], rho, logq, lam, greedy, ts, want_arg=True)
            w = worst_profile(tau, rho, logq, lam, greedy, 24 if quick else 60, ts)
            line = f"rate 2^-{R}, {name} count: tau = {tau:.4f}, regular exponent {reg:+.3f} at (t, r) = {arg}, largest over two-point profiles {w[0]:+.3f}"
            print(line, flush=True)
            if w[1]:
                (w1, d1), (w2, d2) = w[1]
                t, r = arg
                prn, prr = Profile(w[1], t), Profile([(1.0, tau)], t)
                cn = cost_greedy(prn, rho, logq, lam, t) if greedy else cost_note36(prn, rho, logq, lam, t, r)
                cr = cost_greedy(prr, rho, logq, lam, t) if greedy else cost_note36(prr, rho, logq, lam, t, r)
                print(f"    defeating profile: a fraction {w1:.3f} of the coordinates at density {d1:.3f}, {w2:.3f} at density {d2:.3f} (second moment {w1*d1*d1+w2*d2*d2:.4f} <= rho);")
                print(f"    count alone at the regular optimum (t, r) = {arg}: regular {cr:+.3f}, this profile {cn:+.3f}; label entropies {prr.entropy(t):.3f}, {prn.entropy(t):.3f}")
                if not quick:
                    rob = robust_threshold(rho, logq, lam, greedy, treg, min(math.sqrt(rho), treg + 0.03), 30, ts)
                    print(f"    smallest tau at which every two-point profile has a negative exponent: {rob:.4f} ({queries(rob)} queries); regular: {treg:.4f} ({queries(treg)})", flush=True)
            else:
                print("    no two-point profile does worse than the regular one on the grid", flush=True)


if __name__ == "__main__":
    main()
