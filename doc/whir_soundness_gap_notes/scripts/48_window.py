#!/usr/bin/env python3
"""Note 48, parts 2 and 3: the residual analysis for a certificate with B = 2. Exact integers.

  A  Theorem 8'' ingredients: certificate (m0, 2), B_jet, and the Lemma C cuts of note 41 (case I for every
     profile, case II with total contact <= 2n) for b = 1, 2, at n = 2^25..2^28
  B  b = 2, uniform profiles (contact 2j on x n lines): windows without and with Lemma F
  C  b = 2, two contact orders mixed (grid of step 0.05): open cells with Lemma F
  D  b = 1: uniform profiles and the grid contact 2 / contact 4 (and 6), degenerate and non-degenerate
Run: python3 48_window.py [A] [B] [C] [D] [a=0.7065] [lg=25]
"""
import sys
import os
import importlib.util
from math import ceil, log2, isqrt

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("c41", os.path.join(here, "41_counts.py"))
c41 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c41)
R, N = c41.R, c41.N

MS = (12, 16, 20, 24, 30, 40, 60, 80, 120, 240, 480, 960)


def family(b):
    out = []
    for m in MS:
        step = 1 if m <= 120 else (2 if m == 240 else (4 if m == 480 else 8))
        for B in range(b, m // 2 + 1, step):
            out.append((m, B))
    return out


class Ctx:
    def __init__(self, lg, a, m0=None):
        self.n = 1 << lg
        self.D = self.n // 2 + 5
        self.A = ceil(a * self.n)
        self.a = a
        ms = [m for m in range(2, 400) if N(2, m * self.A, self.D) > self.n * R(m, 2)]
        self.cert = ms
        self.m0 = m0 or (ms[0] if ms else None)
        if self.m0:
            self.Wmax = self.m0 * self.A - 1
            self.Bjet = (self.m0 * self.A - 1) // self.D
        self._full = {}

    def full(self, m, B):
        k = (m, B)
        if k not in self._full:
            self._full[k] = N(B, m * self.A, self.D)
        return self._full[k]

    def cut_from(self, prof, b, fam):
        """prof: dict j -> number of lines with contact 2j. Returns (T, pair): the smallest W at which some pair of
        the family satisfies (2) of Lemma C and its side condition, and all intervals [Wc, Wside] found."""
        n, D, A = self.n, self.D, self.A
        best, ivs = None, []
        for (m, B) in fam:
            Wside = m * A - D * (m + B)
            if Wside <= 0:
                continue
            rhs = sum(cnt * (R(m, B) - R(m - 2 * j, B - b)) for j, cnt in prof.items())
            full = self.full(m, B)
            if not full - N(B - b, m * A - Wside, D) > rhs:
                continue
            lo, hi = 0, Wside            # smallest W in (lo, hi] with Phi(W) > rhs
            if full - N(B - b, m * A - 1, D) > rhs:
                hi = 1
            else:
                lo = 1
                while hi - lo > 1:
                    mid = (lo + hi) // 2
                    if full - N(B - b, m * A - mid, D) > rhs:
                        hi = mid
                    else:
                        lo = mid
            ivs.append((hi, Wside, m, B))
            if best is None or hi < best[0]:
                best = (hi, m, B)
        return best, ivs

    def open_segments(self, ivs, lo, hi):
        """the part of [lo, hi] not covered by the union of the intervals [Wc, Wside]: list of (start, end), end exclusive."""
        segs, cur = [], lo
        for (s, e, m, B) in sorted(ivs):
            if e < cur:
                continue
            if s > cur:
                segs.append((cur, min(s, hi + 1)))
            cur = max(cur, e + 1)
            if cur > hi:
                break
        if cur <= hi:
            segs.append((cur, hi + 1))
        return [(x, y) for (x, y) in segs if x < y and x <= hi]


def rho(K, b, j):
    return max(j - K, 2 * j - b - 2 * K, 0)


def nu(b, j):
    return max(j, 2 * j - b)


def smallest_sum(prof, val, A):
    """sum of the A smallest values of val(j) over the lines of the profile (lines outside the profile count val(0))."""
    items = sorted((val(j), cnt) for j, cnt in prof.items())
    tot, left = 0, A
    for v, cnt in items:
        take = min(cnt, left)
        tot += v * take
        left -= take
        if left == 0:
            break
    return tot


def lower_ends(ctx, prof, b, K):
    """lower bounds on W for a case II first integral with deg_{Y0} of the leading coefficient = 2K."""
    n, D, A = ctx.n, ctx.D, ctx.A
    jmax = max(j for j, c in prof.items() if c > 0)
    F2 = (b + 2 * K) * D + sum(c * rho(K, b, j) for j, c in prof.items())
    F3 = b * D + sum(c * rho(K, b, j) for j, c in prof.items()) + smallest_sum(prof, lambda j: nu(b, j) - rho(K, b, j), A)
    M = max(jmax, b + 2 * K) * D
    return F2, F3, M


def old_lower(ctx, prof, b):
    n, D, A = ctx.n, ctx.D, ctx.A
    jmax = max(j for j, c in prof.items() if c > 0)
    return max((b + 2) * D, b * D + smallest_sum(prof, lambda j: nu(b, j), A), jmax * D)


def mkprof(n, parts):
    """parts: list of (j, fraction); the rest of the lines get j = 0."""
    prof, used = {}, 0
    for j, x in parts:
        c = min(int(round(x * n)), n - used)
        prof[j] = prof.get(j, 0) + c
        used += c
    prof[0] = prof.get(0, 0) + n - used
    return prof


def part_A(args):
    print("A. Theorem 8'' ingredients (B = 2 certificates), Delta = n/2 + 5")
    for a in (0.7050, 0.7065):
        for lg in (25, 26, 27, 28):
            ctx = Ctx(lg, a)
            n, D, A = ctx.n, ctx.D, ctx.A
            m0 = ctx.m0
            line = f"   a = {a}, n = 2^{lg}: A = {A}, certificates (m, 2) for m in [{ctx.cert[0]}, {ctx.cert[-1]}], m0 = {m0}, B_jet = {ctx.Bjet}, W_max = m0 A - 1"
            res = {}
            for b in (1, 2):
                fII = fI = None
                for m in range(12, 521):
                    for B in range(b, m // 2 + 1):
                        if fII is None and c41.lemmaC_uniform(n, D, A, b, m, B, ctx.Wmax):
                            fII = (m, B)
                        if fI is None and c41.caseI_all_profiles(n, D, A, b, m, B, ctx.Wmax):
                            fI = (m, B)
                    if fII and fI:
                        break
                res[b] = (fII, fI)
            mcut = max(x[0] for b in res for x in res[b])
            per = (mcut * A - 1) // D
            C = max((ctx.Bjet - t) ** 2 + max(per, 0) * t for t in range(ctx.Bjet + 1))
            print(line)
            print(f"      b = 1: case II with total contact <= 2n cut by {res[1][0]}, case I (every profile) cut by {res[1][1]}")
            print(f"      b = 2: case II with total contact <= 2n cut by {res[2][0]}, case I (every profile) cut by {res[2][1]}")
            print(f"      per unit of degree floor(({mcut} A - 1)/Delta) = {per}; C = max_t (B_jet - t)^2 + {per} t = {C}; queries {ceil(108 / log2(n / A))}")
    # convexity of j -> R(m - 2j, B') used by Lemma U, for the pairs above (m <= 520): checked in 41_counts.py part C


def show(ctx, x):
    return f"{x / ctx.n:.4f}"


def part_B(args, a, lg):
    ctx = Ctx(lg, a)
    n, D, A = ctx.n, ctx.D, ctx.A
    fam = family(2)
    print(f"B. b = 2, case II, uniform profiles: contact 2j on x n lines, none elsewhere; a = {a}, n = 2^{lg}, m0 = {ctx.m0}, W_max = {show(ctx, ctx.Wmax)} n, B_jet = {ctx.Bjet}")
    print("   columns: old lower end (Lemma L, Corollary N, Lemma M) | cut of Lemma C (exact, family of note 48) | per K: lower end with Lemma F | status")
    for j in range(1, 9):
        for x in (0.5, 0.75, 0.9, 0.95, 1.0):
            prof = mkprof(n, [(j, x)])
            best, ivs = ctx.cut_from(prof, 2, fam)
            if best is None:
                print(f"   j = {j}, x = {x}: never cut by the family")
                continue
            T = best[0]
            old = old_lower(ctx, prof, 2)
            oldseg = ctx.open_segments(ivs, old, ctx.Wmax) if old <= ctx.Wmax else []
            cells = []
            for K in range(1, 8):
                F2, F3, M = lower_ends(ctx, prof, 2, K)
                lo = max(F2, F3, M)
                if lo > ctx.Wmax:
                    continue
                segs = ctx.open_segments(ivs, lo, ctx.Wmax)
                if segs:
                    cells.append(f"K={K}: OPEN " + ", ".join(f"[{show(ctx, x)}, {show(ctx, y)})" for x, y in segs))
            if oldseg:
                oldtag = "old tools: open " + ", ".join(f"[{show(ctx, x)}, {show(ctx, y)})" for x, y in oldseg)
                print(f"   j = {j}, x = {x}: {oldtag}; first cut at {show(ctx, T)} n by ({best[1]}, {best[2]}); "
                      + ("with Lemma F: " + "; ".join(cells) if cells else "with Lemma F: CLOSED for every K"))
    print("   (rows not printed: closed already by the old tools)")


def part_C(args, a, lg):
    ctx = Ctx(lg, a)
    n = ctx.n
    fam = [(m, B) for (m, B) in family(2) if m in (16, 24, 40, 80, 240, 960)]
    print(f"C. b = 2, case II, two contact orders 2j1 < 2j2 on x1 n and x2 n lines (step 0.05), none elsewhere; a = {a}, n = 2^{lg}")
    total_open = 0
    stats = []
    for j1 in range(1, 7):
        for j2 in range(j1 + 1, 8):
            opened = []
            for i1 in range(1, 21):
                for i2 in range(1, 21 - i1):
                    x1, x2 = i1 / 20, i2 / 20
                    prof = mkprof(n, [(j1, x1), (j2, x2)])
                    best, ivs = ctx.cut_from(prof, 2, fam)
                    if best is None:
                        opened.append((x1, x2, None, None, None))
                        continue
                    T = best[0]
                    for K in range(1, 8):
                        F2, F3, M = lower_ends(ctx, prof, 2, K)
                        lo = max(F2, F3, M)
                        if lo > ctx.Wmax:
                            continue
                        segs = ctx.open_segments(ivs, lo, ctx.Wmax)
                        if segs:
                            opened.append((x1, x2, K, segs[0][0], segs[0][1]))
            total_open += len(opened)
            for o in opened:
                if o[2]:
                    stats.append((o[0] + o[1], 2 * (j1 * o[0] + j2 * o[1]), o[2], (o[4] - o[3]) / n, min(j1 if o[0] > 0 else j2, j2)))
            if opened:
                ks = sorted({o[2] for o in opened if o[2]})
                wid = max((o[4] - o[3]) / n for o in opened if o[2])
                xs = sorted({(o[0], o[1]) for o in opened})
                print(f"   (j1, j2) = ({j1}, {j2}): {len(xs)} open cells, K in {ks}, largest width {wid:.4f} n, "
                      f"min x1 + x2 = {min(p[0] + p[1] for p in xs):.2f}, cells with the smallest x2: {sorted(xs, key=lambda p: p[1])[:3]}")
    print(f"   total open (cell, K) pairs: {total_open}")
    if stats:
        print(f"   over all open pairs: min fraction of contained lines {min(t[0] for t in stats):.2f}, min mean contact order {min(t[1] for t in stats):.2f}, "
              f"min K {min(t[2] for t in stats)}, largest width {max(t[3] for t in stats):.4f} n")
        k3 = [t for t in stats if t[2] == 3]
        print(f"   pairs with K = 3: {len(k3)}" + (f", largest width {max(t[3] for t in k3):.4f} n" if k3 else ""))


def lemmaB_lower(ctx, prof):
    """b = 1, absolutely irreducible: sum (o^2 - o - 1) <= min(W(W - D)/D, 9W - 25D if W < 6D). Smallest W allowed."""
    D = ctx.D
    s = sum(c * (4 * j * j - 2 * j - 1) for j, c in prof.items() if j >= 1)
    # quintic bound
    Wq = -((-(s + 25 * D)) // 9)
    if Wq < 6 * D:
        # also the general bound must hold; the quintic one is the stronger of the two in this range
        return Wq
    # general: W^2 - D W - s D >= 0
    W = (D + isqrt(D * D + 4 * s * D)) // 2
    while W * (W - D) < s * D:
        W += 1
    return max(W, 6 * D)


def b1_cells(ctx, prof, fam):
    """b = 1, case II: for each K the open segments (tools F, N, M, B and Lemma C), and the same for
    non-degenerate potentials (Theorem 4 of note 45, valid for quintics: K <= 2 and W < 6 Delta)."""
    D = ctx.D
    best, ivs = ctx.cut_from(prof, 1, fam)
    LB = lemmaB_lower(ctx, prof)
    n4 = sum(c for jj, c in prof.items() if jj >= 2)
    n6 = sum(c for jj, c in prof.items() if jj >= 3)
    Tdet = -((-(4 * n4 + 6 * n6 + 8 * D + 1)) // 3)
    out = []
    for K in range(1, 8):
        F2, F3, M = lower_ends(ctx, prof, 1, K)
        lo = max(F2, F3, M, LB)
        if lo > ctx.Wmax:
            continue
        segs = ctx.open_segments(ivs, lo, ctx.Wmax)
        if not segs:
            continue
        if K <= 2:
            non = ctx.open_segments(ivs, max(lo, Tdet), min(ctx.Wmax, 6 * D - 1)) + ctx.open_segments(ivs, max(lo, 6 * D), ctx.Wmax)
        else:
            non = segs
        out.append((K, segs, non))
    return best, out


def fmt(ctx, segs):
    return ", ".join(f"[{show(ctx, x)}, {show(ctx, y)})" for x, y in segs) if segs else "closed"


def part_D(args, a, lg):
    ctx = Ctx(lg, a)
    n, D, A = ctx.n, ctx.D, ctx.A
    fam = family(1)
    print(f"D. b = 1, case II; a = {a}, n = 2^{lg}, W_max = {show(ctx, ctx.Wmax)} n; lower ends: F (Lemma F), N (Corollary N), M, B (Lemma B of note 40); T = Theorem 4 of note 45 (non-degenerate quintics)")
    print("   uniform profiles, contact 2j on x n lines (rows with an open segment only):")
    for j in range(1, 8):
        for x in (0.5, 0.75, 0.9, 0.95, 1.0):
            prof = mkprof(n, [(j, x)])
            best, out = b1_cells(ctx, prof, fam)
            for (K, segs, non) in out:
                print(f"     j = {j}, x = {x}, K = {K}: first cut at {show(ctx, best[0])} n ({best[1]}, {best[2]}); open {fmt(ctx, segs)}; non-degenerate: {fmt(ctx, non)}")
    fam2 = [(m, B) for (m, B) in fam if m in (16, 24, 40, 80, 240, 960)]
    print("   contact 4 on x4 n lines, contact 2 on x2 n lines, none elsewhere (step 0.025):")
    cells, cells_non = [], []
    for i4 in range(0, 41):
        for i2 in range(0, 41 - i4):
            if i4 == 0 and i2 == 0:
                continue
            x4, x2 = i4 / 40, i2 / 40
            prof = mkprof(n, [(2, x4), (1, x2)])
            best, out = b1_cells(ctx, prof, fam2)
            for (K, segs, non) in out:
                cells.append((x4, x2, K, segs))
                if non:
                    cells_non.append((x4, x2, K, non))

    def summ(lst, name):
        if not lst:
            print(f"     {name}: no open cell")
            return
        wid = lambda o: sum(y - x for x, y in o[3]) / n
        print(f"     {name}: {len(lst)} open (cell, K) pairs, K in {sorted({o[2] for o in lst})}; min x4 = {min(o[0] for o in lst):.3f}, "
              f"min x4 + x2 = {min(o[0] + o[1] for o in lst):.3f}, largest total width {max(wid(o) for o in lst):.4f} n")
        for o in sorted(lst, key=lambda o: -wid(o))[:4]:
            print(f"       (x4, x2) = ({o[0]:.3f}, {o[1]:.3f}), K = {o[2]}: {fmt(ctx, o[3])}")
    summ(cells, "degenerate or not (tools F, N, M, B)")
    summ(cells_non, "non-degenerate (also T)")
    print("   contact 6 on x6 n, contact 4 on x4 n, contact 2 on x2 n lines (step 0.05, x6 > 0):")
    cells, cells_non = [], []
    for i6 in range(1, 21):
        for i4 in range(0, 21 - i6):
            for i2 in range(0, 21 - i6 - i4):
                prof = mkprof(n, [(3, i6 / 20), (2, i4 / 20), (1, i2 / 20)])
                best, out = b1_cells(ctx, prof, fam2)
                for (K, segs, non) in out:
                    cells.append((i6 / 20, i4 / 20, i2 / 20, K, segs))
                    if non:
                        cells_non.append((i6 / 20, i4 / 20, i2 / 20, K, non))
    print(f"     open (cell, K) pairs: {len(cells)}; also open for non-degenerate potentials: {len(cells_non)}")
    for o in sorted(cells, key=lambda o: -sum(y - x for x, y in o[4]))[:6]:
        print(f"       (x6, x4, x2) = ({o[0]}, {o[1]}, {o[2]}), K = {o[3]}: {fmt(ctx, o[4])}")


if __name__ == "__main__":
    args = [x for x in sys.argv[1:] if "=" not in x] or ["A", "B", "C", "D"]
    kv = dict(x.split("=") for x in sys.argv[1:] if "=" in x)
    a = float(kv.get("a", "0.7065"))
    lg = int(kv.get("lg", "25"))
    for w in args:
        if w == "A":
            part_A(args)
        elif w == "B":
            part_B(args, a, lg)
        elif w == "C":
            part_C(args, a, lg)
        elif w == "D":
            part_D(args, a, lg)
