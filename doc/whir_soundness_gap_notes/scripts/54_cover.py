#!/usr/bin/env python3
"""54_cover.py: independent re-implementation of the finite part of Theorem 2.1 of note 51 (referee report 54).

Written from the statements of notes 35, 40, 45, 48, 50, 51; it imports nothing from the scripts of those notes.
All arithmetic is in exact integers (a lower bound  den * W >= const + sum_j n_j w_j  is kept as integers, and
den * N_Delta(B, Z) = N_{den Delta}(B, den Z) removes every fraction).

Parts:
  cert    the nine even certificates (inequality (1) of note 50 / (*) of note 52) by direct summation, the bootstrap
          over certificates and the constant (19002 at a = 0.7065), W_max, the cut bound;
  self    self-tests: N against the defining sum, R against the closed form of note 48, the vertex enumeration of a
          cell against an exact fractional-knapsack optimum on random linear forms;
  cover   for each case of the theorem, a covering of the simplex of profiles by cells (dyadic boxes intersected with
          the simplex); a cell is CLOSED only if ONE pair (m, B) and ONE lower bound give g < 0 at EVERY vertex;
  the open cells of the last case, their outer box and their window in W, compared with (D3) of note 51.

Options:  a=0.7065  lg=25  depth=8  mode=M|Mp   (M: j <= delta, Lemma M of note 40, as in note 51;
          Mp: j <= max(K, (D_c + 1) // 2), the sharper bound of report 54)   cases=all|closed|open|name,...
"""
import sys
import random
import time
from fractions import Fraction

# ------------------------------------------------------------------ the two counting functions

_Rcache = {}


def R(m, B):
    """local rank of note 35: sum_{s < m} [(s + 1)(B + 1) - (2s - m + 1)_+ (s + B - m + 1)_+]."""
    if m <= 0 or B < 0:
        return 0
    key = (m, B)
    if key not in _Rcache:
        t = 0
        for s in range(m):
            u, v = 2 * s - m + 1, s + B - m + 1
            t += (s + 1) * (B + 1) - (u * v if (u > 0 and v > 0) else 0)
        _Rcache[key] = t
    return _Rcache[key]


def N_sum(B, Z, D):
    if B < 0 or Z <= 0:
        return 0
    t, tot = 0, 0
    while Z - D * t > 0:
        tot += (min(t, B) + 1) * (Z - D * t)
        t += 1
    return tot


def N(B, Z, D):
    """sum_{t >= 0} (min(t, B) + 1) (Z - D t)_+ for integers; closed form."""
    if B < 0 or Z <= 0:
        return 0
    q = (Z - 1) // D
    if q >= B:
        return (B + 1) * ((q + 1) * Z - D * (q * (q + 1) // 2)) - Z * (B * (B + 1) // 2) + D * ((B - 1) * B * (B + 1) // 6)
    return Z * ((q + 1) * (q + 2) // 2) - D * (q * (q + 1) * (q + 2) // 3)


# ------------------------------------------------------------------ cells

def cell_vertices(lo, hi, U):
    """vertices of {lo <= x <= hi, sum x <= U} (integer data); every vertex is integral."""
    J = len(lo)
    out = set()
    corners = []
    for mask in range(1 << J):
        c = tuple(hi[i] if (mask >> i) & 1 else lo[i] for i in range(J))
        corners.append((mask, c, sum(c)))
    inside = {mask: (s <= U) for mask, c, s in corners}
    for mask, c, s in corners:
        if s <= U:
            out.add(c)
            continue
        for i in range(J):
            if (mask >> i) & 1 and hi[i] > lo[i] and inside[mask ^ (1 << i)]:
                # the edge from this corner down to the corner with x_i = lo_i crosses the hyperplane
                xi = U - (s - c[i])
                out.add(c[:i] + (xi,) + c[i + 1:])
    return sorted(out)


def knapsack_max(cost, lo, hi, U):
    """max of cost . x over the cell, exactly (fractional knapsack after the shift x = lo + z)."""
    cap = U - sum(lo)
    if cap < 0:
        return None
    val = Fraction(sum(c * l for c, l in zip(cost, lo)))
    items = sorted(((c, h - l) for c, l, h in zip(cost, lo, hi) if c > 0), reverse=True)
    for c, w in items:
        take = min(w, cap)
        val += c * take
        cap -= take
    return val


def selftests():
    rng = random.Random(54)
    for _ in range(4000):
        B, D = rng.randint(0, 40), rng.randint(2, 60)
        Z = rng.randint(-5, 70 * D)
        assert N(B, Z, D) == N_sum(B, Z, D), (B, Z, D)
    for m in range(1, 70):
        for B in range(0, (m + 1) // 2 + 1):
            if m >= 2 * B - 1:
                closed = Fraction(B + 1) * (Fraction(m * (m + 1), 2) - Fraction(m * B, 2) + Fraction(B * (2 * B + 1), 6))
                assert closed == R(m, B), (m, B)
    for _ in range(3000):
        J = rng.randint(1, 6)
        U = rng.randint(1, 40)
        lo = [rng.randint(0, U) for _ in range(J)]
        hi = [l + rng.randint(0, 12) for l in lo]
        vs = cell_vertices(lo, hi, U)
        if sum(lo) > U:
            assert not vs
            continue
        assert vs and all(sum(v) <= U and all(l <= x <= h for x, l, h in zip(v, lo, hi)) for v in vs)
        for _ in range(4):
            cost = [rng.randint(-9, 9) for _ in range(J)]
            assert max(sum(c * x for c, x in zip(cost, v)) for v in vs) == knapsack_max(cost, lo, hi, U), (lo, hi, U, cost)
    print("self-tests: N closed form = defining sum (4000 arguments); R = closed form of note 48 for m >= 2B - 1, m < 70;")
    print("            cell vertices: the maximum of 12000 random linear forms over the vertex set = the exact knapsack optimum")


# ------------------------------------------------------------------ certificates and the bootstrap

CERTS = {
    "0.7065": [(2, 17), (4, 23), (8, 40), (16, 74), (32, 144), (64, 284), (128, 564), (256, 1123), (512, 2242)],
    "0.705": [(4, 26), (8, 44), (16, 81), (32, 155), (64, 305), (128, 604), (256, 1203), (512, 2401)],
}


def certificates(n, D, A, pairs):
    """checks (*) for each (q, m) by the defining sums; returns (W_max, d_first, threshold, delta_max)."""
    N0 = lambda Z: N_sum(0, Z, D)
    rows = []
    for q, m in pairs:
        assert m >= 2 * q - 1
        lhs = N0(m * A) + N0(m * A - q * D)
        rhs = n * (m * m - (q - 1) * m + q * (3 * q - 1) // 2)
        d = (m * A - 1) // D
        rows.append((q, m, d, lhs - rhs, (m * A - 1) // q))
        assert lhs > rhs, "not a certificate: (%d, %d)" % (q, m)
    # bootstrap: the first certificate gives one survivor with q delta <= d; each further certificate applies to it as
    # soon as |L| > delta d with the bound on delta known at that point
    q0, m0, d0 = rows[0][0], rows[0][1], rows[0][2]
    delta = d0 // q0
    thr = 0
    chain = [delta]
    for q, m, d, _, _ in rows[1:]:
        thr = max(thr, delta * d)
        delta = min(delta, d // q)
        chain.append(delta)
    Wmax = min(r[4] for r in rows)
    return rows, Wmax, d0, thr, delta, chain


# ------------------------------------------------------------------ lower bounds (integers: den W >= const + sum n_j w_j)

def rhoK(K, j):
    return max(j - K, 2 * j - 1 - 2 * K, 0)


def lower_bounds(K, Dc, kind, J, D, A):
    out = [("floor", 1, max(2 * K + 1, Dc) * D, [0] * (J + 1))]
    out.append(("L1", 1, (2 * K + 1) * D, [rhoK(K, j) for j in range(J + 1)]))
    cK = [max(2 * j - 1, 0) - rhoK(K, j) for j in range(J + 1)]
    assert all(c >= 0 for c in cK)
    for lam in sorted(set(c for c in cK if c > 0)):
        out.append(("L2(%d)" % lam, 1, D + lam * A, [rhoK(K, j) - max(lam - cK[j], 0) for j in range(J + 1)]))
    out.append(("B", 2 * K + Dc, D * Dc * (1 + 2 * K), [max(4 * j * j - 2 * j - 1, 0) for j in range(J + 1)]))
    if kind == "nondeg":
        out.append(("T", 3, 8 * D + 1, [2 * (3 * j - 4) if j >= 2 else 0 for j in range(J + 1)]))
    if kind == "dep":
        for lam in range(1, J + 1):
            out.append(("D(%d)" % lam, 1, 3 * D + lam * A, [-max(lam - j, 0) for j in range(J + 1)]))
    return out


class Case:
    def __init__(self, name, K, Dc, kind, n, D, A, Wmax, mode, ms):
        self.name, self.K, self.Dc, self.kind = name, K, Dc, kind
        self.n, self.D, self.A, self.Wmax = n, D, A, Wmax
        self.J = max(2 * K + 1, Dc) if mode == "M" else max(K, (Dc + 1) // 2)
        self.bounds = lower_bounds(K, Dc, kind, self.J, D, A)
        self.cands = []
        for m in ms:
            step = max(1, m // 120)
            for B in range(1, m // 2 + 1, step):
                if D * (m + B) <= m * A - Wmax:              # side condition of Lemma C at the largest W
                    psi = [R(m, B) - R(m - 2 * j, B - 1) for j in range(self.J + 1)]
                    assert all(psi[j] <= psi[j + 1] for j in range(self.J))
                    self.cands.append((m, B, psi, N(B, m * A, D)))
        self.pairs = [(ci, bi) for ci in range(len(self.cands)) for bi in range(len(self.bounds))]
        self.recent = []
        self.used = {}
        self.nev = 0

    def G(self, ci, bi, prof):
        """den * (sum_j n_j psi(j) - Phi(l(n))) : the profile is cut by ((m, B), l) iff this is < 0."""
        m, B, psi, NB = self.cands[ci]
        _, den, const, w = self.bounds[bi]
        num = const + sum(wj * nj for wj, nj in zip(w, prof))           # den * (lower bound on W)
        self.nev += 1
        return den * (sum(p * nj for p, nj in zip(psi, prof)) - NB) + N(B - 1, den * m * self.A - num, den * self.D)

    def close(self, profs):
        for pr in self.recent:
            if all(self.G(pr[0], pr[1], p) < 0 for p in profs):
                return pr
        J1 = self.J + 1
        ctr = [sum(p[j] for p in profs) // len(profs) for j in range(J1)]
        ctr[0] += self.n - sum(ctr)
        scored = []
        for ci, bi in self.pairs:
            v = self.G(ci, bi, ctr)
            if v < 0:
                m = self.cands[ci][0]
                scored.append((Fraction(v, self.bounds[bi][1] * m ** 3), ci, bi))
        scored.sort()
        for _, ci, bi in scored[:30]:
            if all(self.G(ci, bi, p) < 0 for p in profs):
                pr = (ci, bi)
                self.recent = [pr] + [r for r in self.recent if r != pr][:11]
                return pr
        return None

    def run(self, depth):
        U = 1 << depth
        sc = self.n // U
        J = self.J
        stack = [((0,) * J, (U,) * J)]
        ncells, opened = 0, []
        while stack:
            lo, hi = stack.pop()
            vs = cell_vertices(lo, hi, U)
            if not vs:
                continue
            ncells += 1
            profs = [[(U - sum(v)) * sc] + [x * sc for x in v] for v in vs]
            pr = self.close(profs)
            if pr is not None:
                key = (self.cands[pr[0]][0], self.cands[pr[0]][1], self.bounds[pr[1]][0])
                self.used[key] = self.used.get(key, 0) + 1
                continue
            widths = [h - l for l, h in zip(lo, hi)]
            wmax = max(widths)
            if wmax <= 1:
                opened.append((lo, hi, profs))
                continue
            i = max(k for k in range(J) if widths[k] == wmax)          # bisect the widest side, highest j first
            mid = (lo[i] + hi[i]) // 2
            stack.append((lo, hi[:i] + (mid,) + hi[i + 1:]))
            stack.append((lo[:i] + (mid,) + lo[i + 1:], hi))
        return ncells, opened

    def window(self, profs):
        """every first integral of this case with profile in the cell that is not cut has W in [wl, wh)."""
        wl = 0
        for _, den, const, w in self.bounds:
            v = min(const + sum(wj * nj for wj, nj in zip(w, p)) for p in profs)   # exact minimum over the cell
            wl = max(wl, -((-v) // den))
        wh = self.Wmax + 1
        for m, B, psi, NB in self.cands:
            if m != max(c[0] for c in self.cands):
                continue
            cred = max(sum(pj * nj for pj, nj in zip(psi, p)) for p in profs)       # exact maximum over the cell
            a_, b_ = wl, wh
            while a_ < b_:
                mid = (a_ + b_) // 2
                if NB - N(B - 1, m * self.A - mid, self.D) > cred:
                    b_ = mid
                else:
                    a_ = mid + 1
            wh = min(wh, b_)
        return wl, wh

    def threshold(self, prof):
        """smallest W at which the integer profile is cut by some candidate (the cut of Lemma C for that profile)."""
        best = None
        for m, B, psi, NB in self.cands:
            cred = sum(pj * nj for pj, nj in zip(psi, prof))
            a_, b_ = 0, self.Wmax + 1
            while a_ < b_:
                mid = (a_ + b_) // 2
                if NB - N(B - 1, m * self.A - mid, self.D) > cred:
                    b_ = mid
                else:
                    a_ = mid + 1
            if best is None or b_ < best[0]:
                best = (b_, m, B)
        return best


def random_profiles(rng, n, J, count, focus=None):
    """integer profiles (n_0..n_J) summing to n: sparse supports, near-vertex profiles, and profiles near `focus`."""
    out = []
    for t in range(count):
        kind = t % 4
        w = [0.0] * (J + 1)
        if kind == 0:
            for j in rng.sample(range(J + 1), rng.randint(1, J + 1)):
                w[j] = rng.expovariate(1.0)
        elif kind == 1:
            j0 = rng.randrange(J + 1)
            w[j0] = 1.0
            for j in rng.sample(range(J + 1), rng.randint(1, J + 1)):
                w[j] += rng.random() * rng.choice([0.002, 0.01, 0.05, 0.2])
        elif kind == 2:
            w = [rng.random() ** 3 for _ in range(J + 1)]
        else:
            j0 = focus if focus is not None else rng.randrange(J + 1)
            w[j0] = 1.0
            for j in range(J + 1):
                if j != j0 and rng.random() < 0.6:
                    w[j] = rng.random() * rng.choice([0.001, 0.004, 0.01, 0.03, 0.08])
        tot = sum(w)
        prof = [int(n * x / tot) for x in w]
        prof[max(range(J + 1), key=lambda j: prof[j])] += n - sum(prof)
        out.append(prof)
    return out


def pointwise(cs, prof):
    """direct check, without convexity: at the largest lower bound on W, is the profile cut by some candidate?"""
    lb = max(-((-(const + sum(wj * nj for wj, nj in zip(wv, prof)))) // den) for _, den, const, wv in cs.bounds)
    if lb > cs.Wmax:
        return "impossible", lb
    for m, B, psi, NB in cs.cands:
        if NB - N_sum(B - 1, m * cs.A - lb, cs.D) > sum(pj * nj for pj, nj in zip(psi, prof)):
            return "cut", lb
    return "uncut", lb


def sample_check(cs, opened, U, rng, count):
    """every sampled profile must be impossible, cut, or (open case only) inside one of the open cells."""
    res = {"impossible": 0, "cut": 0, "uncut": 0}
    bad = 0
    for prof in random_profiles(rng, cs.n, cs.J, count, focus=2 if opened else None):
        st, lb = pointwise(cs, prof)
        res[st] += 1
        if st == "uncut":
            # the profile must lie in an open cell (closed boxes, coordinates in units of n / U)
            sc = cs.n // U
            if not any(all(l * sc <= x <= h * sc for x, l, h in zip(prof[1:], o[0], o[1])) for o in opened):
                bad += 1
    return res, bad


CASES = [
    ("K0 Dc<=1", 0, 1, "gen"), ("K0 Dc=2", 0, 2, "gen"), ("K0 Dc=3", 0, 3, "gen"), ("K0 Dc=4", 0, 4, "gen"),
    ("K0 Dc=5", 0, 5, "gen"), ("K0 Dc=6", 0, 6, "gen"),
    ("cubic (K1 Dc<=3)", 1, 3, "gen"), ("K1 Dc=4", 1, 4, "gen"), ("K1 Dc=5", 1, 5, "gen"), ("K1 Dc=6", 1, 6, "gen"),
    ("sextic (K2 Dc=6)", 2, 6, "gen"),
    ("nondegenerate quintic (K2 Dc<=5, det != 0)", 2, 5, "nondeg"),
    ("dependent quintic (K2 Dc<=5)", 2, 5, "dep"), ("dependent (K2 Dc=6)", 2, 6, "dep"),
    ("OPEN: K2 Dc<=5, det = 0, A and B independent", 2, 5, "gen"),
]


def main():
    opt = dict(a="0.7065", lg="25", depth="8", mode="M", cases="all", part="all")
    for arg in sys.argv[1:]:
        k, v = arg.split("=", 1)
        opt[k] = v
    a = Fraction(opt["a"])
    lg, depth, mode = int(opt["lg"]), int(opt["depth"]), opt["mode"]
    n = 1 << lg
    D = n // 2 + 5
    A = -((-a.numerator * n) // a.denominator)
    t0 = time.time()
    print("=== 54_cover.py a=%s lg=%d depth=%d mode=%s cases=%s" % (opt["a"], lg, depth, mode, opt["cases"]))
    if opt["part"] in ("all", "self"):
        selftests()
    rows, Wmax, d0, thr, delta, chain = certificates(n, D, A, CERTS[opt["a"]])
    print("n = 2^%d, Delta = %d, A = %d" % (lg, D, A))
    for q, m, d, margin, wq in rows:
        print("   certificate (q, m) = (%d, %d): margin of (*) %d = %.5f n, d = %d, d // q = %d, (mA - 1) // q = %d = %.4f n"
              % (q, m, margin, margin / n, d, d // q, wq, wq / n))
    cutb = delta * ((960 * A - 1) // D)
    print("   bootstrap: delta <= %s; the survivor satisfies all certificates as soon as |L| > %d; list bound %d^2 + %d = %d"
          % (chain, thr, d0, thr, d0 * d0 + thr))
    print("   W_max = %d = %.5f n; 6 Delta = %d; cut bound delta * floor((960 A - 1)/Delta) = %d * %d = %d  (%s the threshold)"
          % (Wmax, Wmax / n, 6 * D, delta, (960 * A - 1) // D, cutb, "below" if cutb < thr else "NOT BELOW"))
    assert delta == 6 and cutb < thr
    if opt["part"] == "cert":
        return
    ms = (960, 480, 240, 120, 60, 30)
    sel = opt["cases"]
    U = 1 << depth
    for name, K, Dc, kind in CASES:
        is_open = name.startswith("OPEN")
        if sel == "closed" and is_open:
            continue
        if sel == "open" and not is_open:
            continue
        if sel not in ("all", "closed", "open") and not any(s in name for s in sel.split(",")):
            continue
        if max(2 * K + 1, Dc) * D > Wmax:
            print("case %s: floor above W_max, empty" % name)
            continue
        t1 = time.time()
        cs = Case(name, K, Dc, kind, n, D, A, Wmax, mode, ms)
        ncells, opened = cs.run(depth)
        top = sorted(cs.used.items(), key=lambda kv: -kv[1])[:4]
        print("case %s: j <= %d, %d candidates (m, B), %d bounds, %d cells, %d open cells of side 1/%d, %d evaluations  [%.0f s]"
              % (name, cs.J, len(cs.cands), len(cs.bounds), ncells, len(opened), U, cs.nev, time.time() - t1))
        print("      most used: " + ", ".join("(%d, %d, %s) x%d" % (k[0], k[1], k[2], v) for k, v in top))
        if opened and not is_open:
            print("      *** NOT CLOSED ***")
        if opened:
            J = cs.J
            for j in range(1, J + 1):
                print("      open cells: %d/%d <= x_%d <= %d/%d" % (min(o[0][j - 1] for o in opened), U, j, max(o[1][j - 1] for o in opened), U))
            x0max = max(max(p[0] for p in o[2]) for o in opened)
            print("      open cells: x_0 <= %d/%d" % (x0max * U // n, U))
            wl, wh = None, 0
            for lo, hi, profs in opened:
                l_, h_ = cs.window(profs)
                if h_ > l_:
                    wl = l_ if wl is None else min(wl, l_)
                    wh = max(wh, h_)
            print("      window over the open cells: %d <= W < %d, that is [%.5f, %.5f) n" % (wl, wh, wl / n, wh / n))
            if mode == "M" and U <= 256:
                # the outer box and window of the open cells printed by 51_profiles.py (51_results.txt), in 1/256
                if opt["a"] == "0.7065":
                    box, x0b, win = {1: (0, 22), 2: (233, 256), 3: (0, 11), 4: (0, 3), 5: (0, 2)}, 6, {25: (84235620, 92960839), 26: (168471225, 185921635), 27: (336942436, 371843225), 28: (673884857, 743686395)}
                else:
                    box, x0b, win = {1: (0, 30), 2: (222, 256), 3: (0, 16), 4: (0, 5), 5: (0, 3)}, 8, {25: (83886105, 94276015), 26: (167772185, 188551983), 27: (335544345, 377103927), 28: (671088665, 754207815)}
                sc = 256 // U
                inside = all(box[j][0] <= o[0][j - 1] * sc and o[1][j - 1] * sc <= box[j][1] for o in opened for j in range(1, J + 1))
                print("      all open cells inside the box of note 51 (%s; x_0 <= %d/256): %s; window inside the window of note 51 [%d, %d): %s"
                      % (", ".join("%d/256 <= x_%d <= %d/256" % (box[j][0], j, box[j][1]) for j in sorted(box)), x0b,
                         inside and x0max * 256 <= x0b * n, win[lg][0], win[lg][1], win[lg][0] <= wl and wh <= win[lg][1]))
        if opt.get("sample", "0") != "0":
            res, bad = sample_check(cs, opened, U, random.Random(540 + len(name)), int(opt["sample"]))
            print("      pointwise check on %d random profiles (no convexity, defining sums): %d impossible (lower bound above W_max), %d cut, %d not cut%s"
                  % (sum(res.values()), res["impossible"], res["cut"], res["uncut"],
                     (", of which %d OUTSIDE the open cells  *** ERROR ***" % bad) if bad else (", all inside the open cells" if res["uncut"] else "")))
        if is_open or "cubic" in name:
            # the uniform profile: contact 4 on all lines
            if cs.J >= 2:
                prof = [0] * (cs.J + 1)
                prof[2] = n
                w, m, B = cs.threshold(prof)
                lb = max(-((-(const + sum(wj * nj for wj, nj in zip(wv, prof)))) // den) for _, den, const, wv in cs.bounds)
                print("      contact 4 on all lines: largest lower bound %d = %.5f n; first cut at W = %d = %.5f n by (%d, %d)" % (lb, lb / n, w, w / n, m, B))
    print("total %.0f s" % (time.time() - t0))


if __name__ == "__main__":
    main()
