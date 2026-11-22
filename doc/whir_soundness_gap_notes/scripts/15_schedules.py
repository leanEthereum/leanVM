#!/usr/bin/env python3
"""Researcher 15: point schedules for the DEEP-fold level (note 15, Lemma S and section 6).

A level has ell fold rounds. A schedule is a set of batches; batch b (1 <= b <= ell) has s_b points, sampled after
the fold challenge of round b - 1 (batch 1: after the commitment), answered on the current tuple and carried to the end
of the level. Round j uses the batches of an interval [f_j, j]. Lemma S of note 15 gives, per batch message f,

    [f = 1: C(L,2) eps^s_1]  +  delta'_f  +  sum_{j : f_j = f}  C1 * eps^(sum of s_b, b in S_j) * tau^-(j - f) * prod_{b in S_j, b > f} 1/delta'_b
        <=  2^-(125 - grind of the message)

with C1 = 4 L^3 q^6 / K0^3 (Lemma D4 of note 11), delta'_b > 0 when a round that started earlier also uses batch b (the
whole budget of the message when no round starts at b, half of it otherwise; absent when no earlier round uses b), and
K0/q^2 + tau <= 2^-(125 - g_fold) for the fold challenges. A batch after the first has its own grind g_mid (default:
the point grind; 0 means its message carries no nonce). All arithmetic in log2 (floats). `c1="pair"` replaces C1 by
C(L,2): the hypothetical in which the third-moment factor q^3 is gone and only the pinning count is left.

The ladder (Lemma S of note 15, the recommended design): every batch after the first is a top-up sent in the same
verifier message as the preceding fold challenge, and every round uses all the points sampled so far. Then no batch
after the first has a budget of its own, and the condition is

    C(L,2) eps^s_1  +  sum_j  C1 * eps^(s_1 + .. + s_j) * tau^-(j - 1)   <=  2^-(125 - g_pt).

`ladder()` starts from the least cumulative counts with every term within an equal share of the budget and then removes
or delays points one at a time while the exact sum stays within the budget. Fewer points by every round means less
prover work, fewer scalars and less verifier work at once.

Costs. Level 0 (kappa = 24, ell = 6, mu = 30): a point of batch 1 is 2^mu products K x E (2 carry-less multiplications
each); a point of batch b >= 2 is 2^(mu-b+1) products E x E (3 each, Karatsuba, accumulated unreduced). The level-0 NTT
at rate 1/2 has kappa/2 * 2^(mu+1) = 24 * 2^mu multiplications. So a point costs 1/12 of it in batch 1 and
2^-(b-1) / 8 in batch b >= 2 (half of these at rate 1/4, and so on). At a later level every lane is E-valued: a point of
batch b is 3 * 2^(kappa+ell-b+1) carry-less multiplications. A point of batch b costs ell - b + 2 scalars (its answer
and one value per remaining round), and the verifier about 2 kappa + ell + 3 + 3 (ell - b + 1) products in E (the chain
of the subspace polynomials, the terminal product, the conversion, the per-round updates; a formula count).

Usage: python3 15_schedules.py            tables of note 15
       python3 15_schedules.py selftest   reproduces the single-batch point counts of notes 10 and 11
"""
import itertools
import math
import sys

LOGQ = 128.0
MU = 30


def log2add(a, b):
    if a < b:
        a, b = b, a
    return a + math.log2(1.0 + 2.0 ** (b - a))


class Level:
    def __init__(self, kappa, ell, lam, g_fold=7, g_pt=15, c1="d4", g_mid=None, level0=True):
        self.kappa, self.ell, self.lam, self.level0 = kappa, ell, lam, level0
        d = 2**kappa - 1 + ell
        self.leps = math.log2(d + 2**ell) - LOGQ  # log2 eps
        self.lk0 = g_fold + 2 + LOGQ  # K0 = 2^(g+2) q
        self.ltau = -(126.0 - g_fold)  # tau = 2^-(126-g): K0/q^2 + tau = 2^-(125-g)
        self.lbud = -(125.0 - g_pt)
        self.lmid = -(125.0 - (g_pt if g_mid is None else g_mid))
        if c1 == "d4":
            self.lc1 = 2 + 3 * lam + 6 * LOGQ - 3 * self.lk0
        elif c1 == "pair":
            self.lc1 = 2 * lam - 1
        else:
            raise ValueError(c1)
        self.lpin = 2 * lam - 1  # C(L,2)

    def bud(self, b):
        return self.lbud if b == 1 else self.lmid

    def ldp(self, bs, first):
        """log2 delta'_b: None when no earlier round uses batch b."""
        out = {}
        for b in bs:
            old = any(first[j] < b for j in range(b, self.ell + 1))
            enters = any(first[j] == b for j in range(b, self.ell + 1))
            out[b] = None if not old else (self.bud(b) - 1.0 if enters else self.bud(b))
        return out

    def term(self, sizes, bs, ldp, j, f):
        sj = [b for b in bs if f <= b <= j]
        return self.lc1 + sum(sizes[b] for b in sj) * self.leps - (j - f) * self.ltau - sum(ldp[b] for b in sj if b > f)

    def check(self, sizes, first):
        """sizes: dict b -> s_b (b = 1 present). first: dict j -> f_j. Returns the smallest slack in bits (>= 0 iff valid)."""
        bs = sorted(sizes)
        ldp = self.ldp(bs, first)
        slack = 1e9
        for f in bs:
            tot = self.lpin + sizes[1] * self.leps if f == 1 else None
            for j in range(f, self.ell + 1):
                if first[j] == f:
                    t = self.term(sizes, bs, ldp, j, f)
                    tot = t if tot is None else log2add(tot, t)
            if tot is None:
                continue  # the message's error is delta'_f alone, the whole budget
            room = self.bud(f) if ldp[f] is None else self.bud(f) - 1.0  # what delta'_f leaves
            slack = min(slack, room - tot)
        return slack

    def prover(self, sizes):
        """Carry-less multiplications over the level-0 NTT's multiplications at rate 1/2 (24 * 2^mu)."""
        tot = 0.0
        for b, s in sizes.items():
            if self.level0 and b == 1:
                tot += s * 2.0 * 2.0**MU
            else:
                tot += s * 3.0 * 2.0 ** (self.kappa + self.ell - b + 1)
        return tot / (24.0 * 2.0**MU)

    def scalars(self, sizes):
        return sum(s * (self.ell - b + 2) for b, s in sizes.items())

    def vmults(self, sizes):
        return sum(s * (2 * self.kappa + self.ell + 3 + 3 * (self.ell - b + 1)) for b, s in sizes.items())


def monotone_firsts(bs, ell):
    """All assignments j -> f_j with f_j a batch <= j, non-decreasing in j."""
    def rec(j, lo):
        if j > ell:
            yield {}
            return
        for f in bs:
            if lo <= f <= j:
                for rest in rec(j + 1, f):
                    d = {j: f}
                    d.update(rest)
                    yield d
    yield from rec(1, 1)


def min_sizes(L, bs, first, cost, smax=26, best=float("inf")):
    """Smallest-cost sizes for a fixed structure, by depth-first search over the batches in order."""
    res = [best, None]
    ldp = L.ldp(bs, first)

    def rec(i, cur):
        if i == len(bs):
            c = cost(cur)
            if c < res[0] and L.check(cur, first) >= 0:
                res[0], res[1] = c, dict(cur)
            return
        b = bs[i]
        for s in range(1, smax + 1):
            cur[b] = s
            if cost(cur) >= res[0]:
                break
            # necessary: the rounds before the next batch only involve the batches assigned so far
            nxt = bs[i + 1] if i + 1 < len(bs) else L.ell + 1
            if all(L.term(cur, bs[: i + 1], ldp, j, first[j]) <= L.bud(first[j]) for j in range(b, nxt)):
                rec(i + 1, cur)
        cur.pop(b, None)

    rec(0, {})
    return res


def best_schedule(L, cost, max_batches=None):
    best = (float("inf"), None, None)
    for k in range(0, L.ell):
        if max_batches is not None and k + 1 > max_batches:
            break
        for extra in itertools.combinations(range(2, L.ell + 1), k):
            bs = [1] + list(extra)
            for first in monotone_firsts(bs, L.ell):
                c, sizes = min_sizes(L, bs, first, cost, best=best[0])
                if sizes is not None and c < best[0]:
                    best = (c, sizes, first)
    return best


def single(L):
    f = {j: 1 for j in range(1, L.ell + 1)}
    return min_sizes(L, [1], f, lambda b: sum(b.values()))[1], f


def fresh(L):
    bs = list(range(1, L.ell + 1))
    f = {j: j for j in bs}
    return min_sizes(L, bs, f, lambda b: sum(b.values()))[1], f


def ladder_error(L, cum):
    """log2 of the first batch's message error for cumulative counts cum[0..ell-1]."""
    tot = L.lpin + cum[0] * L.leps
    for j in range(1, L.ell + 1):
        tot = log2add(tot, L.lc1 + cum[j - 1] * L.leps - (j - 1) * L.ltau)
    return tot


def ladder(L):
    """Cumulative point counts sigma_1 <= .. <= sigma_ell, locally minimal; returns the batch sizes and the slack in bits."""
    ell = L.ell
    share = L.lbud - math.log2(ell)
    cum = []
    for j in range(1, ell + 1):
        sig = max(cum[-1] if cum else 1, 1)
        while L.lc1 + sig * L.leps - (j - 1) * L.ltau > share - (1.0 if j == 1 else 0.0):
            sig += 1
        cum.append(sig)
    improved = True
    while improved:
        improved = False
        for j in list(range(ell - 1, -1, -1)):  # the last round first: that removes a point, the others delay one
            lo = cum[j - 1] if j > 0 else 1
            if cum[j] - 1 >= lo:
                trial = cum[:j] + [cum[j] - 1] + cum[j + 1:]
                if ladder_error(L, trial) <= L.lbud:
                    cum, improved = trial, True
                    break
    sizes, prev = {}, 0
    for j in range(1, ell + 1):
        if cum[j - 1] > prev:
            sizes[j] = cum[j - 1] - prev
        prev = cum[j - 1]
    return sizes, L.lbud - ladder_error(L, cum)


def describe_ladder(L, sizes, slack):
    bs = sorted(sizes)
    cum, c = [], 0
    for j in range(1, L.ell + 1):
        c += sizes.get(j, 0)
        cum.append(c)
    return "batches %s | points %d | scalars %d | bytes %d | prover %.4f NTT0 | verifier E-products %d | extra messages 0 | slack %.1f bits | points available per round %s" % (
        " ".join("%d@%d" % (sizes[b], b) for b in bs), sum(sizes.values()), L.scalars(sizes), 16 * L.scalars(sizes), L.prover(sizes), L.vmults(sizes), slack,
        " ".join(str(x) for x in cum))


def describe(L, sizes, first):
    bs = sorted(sizes)
    use = " ".join("%d:[%s]" % (j, ",".join(str(b) for b in bs if first[j] <= b <= j)) for j in range(1, L.ell + 1))
    nonces = sum(1 for b in bs if b > 1 and L.lmid > -125.0)
    return "batches %s | points %d | scalars %d | bytes %d | prover %.4f NTT0 | verifier E-products %d | extra messages %d | slack %.1f bits | rounds use %s" % (
        " ".join("%d@%d" % (sizes[b], b) for b in bs), sum(sizes.values()), L.scalars(sizes), 16 * L.scalars(sizes) + 8 * nonces,
        L.prover(sizes), L.vmults(sizes), len(bs) - 1, L.check(sizes, first), use)


def table(kappa, ell, lams, c1, level0):
    L0 = Level(kappa, ell, 0, c1=c1, level0=level0)
    print("\n### kappa = %d, ell = %d, %s, C1 = %s, eps = 2^%.2f" % (
        kappa, ell, "level 0 (K-valued lanes)" if level0 else "later level (E-valued lanes)",
        "4 L^3 q^6 / K0^3 (Lemma D4)" if c1 == "d4" else "C(L,2) (hypothetical: no q^3)", L0.leps))
    for lam in lams:
        L = Level(kappa, ell, lam, c1=c1, level0=level0)
        print("- list 2^%d:" % lam)
        sz, f = single(L)
        base = sz
        print("    D   one batch (note 11)        %s" % describe(L, sz, f))
        lsz, lslack = ladder(L)
        print("    Ld  ladder (top-ups with c_j)  %s" % describe_ladder(L, lsz, lslack))
        sz, f = fresh(L)
        print("    F   fresh every round          %s" % describe(L, sz, f))
        tie = lambda b: 1e-6 * L.scalars(b)
        if level0:
            c, sz, f = best_schedule(L, lambda b: L.prover(b) + tie(b), max_batches=2)
            print("    T2  two batches, least prover  %s" % describe(L, sz, f))
            L2 = Level(kappa, ell, lam, c1=c1, level0=level0, g_mid=0)
            c, sz2, f2 = best_schedule(L2, lambda b: L2.prover(b) + tie(b), max_batches=2)
            print("    T2' the same, no grind at 2nd  %s" % describe(L2, sz2, f2))
            c, sz, f = best_schedule(L, lambda b: L.prover(b) + tie(b))
            print("    P   least prover work          %s" % describe(L, sz, f))
        c, sz, f = best_schedule(L, lambda b: L.scalars(b) + 1e-3 * sum(b.values()))
        print("    S   fewest scalars             %s" % describe(L, sz, f))
        print("    A   full columns               points %d | scalars %d | bytes %d | prover %.4f NTT0 (the sizes of D: section 5.1)" % (
            base[1], base[1] * 2**ell, 16 * base[1] * 2**ell, L.prover(base)))


def opening(lam, c1):
    """mu = 30: levels (kappa, ell) = (24,6), (20,4), (16,4), (12,4), (8,4), (4,4), the same list bound at every level."""
    shapes = [(24, 6), (20, 4), (16, 4), (12, 4), (8, 4), (4, 4)]
    rows = {}
    for name in ("D", "ladder", "T2 at level 0", "F"):
        pts, sc, pr, vm = [], 0, 0.0, 0
        for i, (kappa, ell) in enumerate(shapes):
            L = Level(kappa, ell, lam, c1=c1, level0=(i == 0))
            if name == "F":
                sz, f = fresh(L)
            elif name == "ladder":
                sz, _ = ladder(L)
            elif name == "T2 at level 0" and i == 0:
                _, sz, f = best_schedule(L, lambda b: L.prover(b) + 1e-6 * L.scalars(b), max_batches=2)
            else:
                sz, f = single(L)
            pts.append("+".join(str(sz[b]) for b in sorted(sz)))
            sc += L.scalars(sz)
            pr += L.prover(sz)
            vm += L.vmults(sz)
        rows[name] = (pts, sc, pr, vm)
    print("- list 2^%d at every level, C1 = %s:" % (lam, c1))
    for name, (pts, sc, pr, vm) in rows.items():
        print("    %-14s points per level %s | scalars %d (%d B) | prover %.4f NTT0 | verifier E-products %d" % (name, " ".join(pts), sc, 16 * sc, pr, vm))


def selftest():
    want = {(24, 6): {10: 11, 40: 12, 70: 13, 100: 14, 334: 20}, (20, 4): {10: 8, 40: 9, 70: 10, 100: 11, 334: 17},
            (12, 4): {10: 8, 40: 9, 70: 9, 100: 10, 334: 16}, (4, 4): {10: 7, 40: 8, 70: 9, 100: 10, 334: 15}}
    ok = True
    for (kappa, ell), row in want.items():
        for lam, s in row.items():
            got = single(Level(kappa, ell, lam))[0][1]
            ok = ok and got == s
            print("kappa %2d ell %d list 2^%-3d: %2d points (note 11, table T1: %2d) %s" % (kappa, ell, lam, got, s, "ok" if got == s else "MISMATCH"))
    L = Level(24, 6, 0)
    print("bits needed at level 0, L = 1 (largest term): %.1f (note 11: 1064)" % (L.lc1 - 5 * L.ltau - L.lbud))
    # a schedule is valid iff every message is within budget when recomputed directly
    L = Level(24, 6, 40)
    sizes, first = {1: 8, 4: 5}, {1: 1, 2: 1, 3: 1, 4: 1, 5: 1, 6: 1}
    direct = None
    for j in range(1, 7):
        s = 8 if j < 4 else 13
        t = L.lc1 + s * L.leps + (j - 1) * 119.0 + (110.0 if j >= 4 else 0.0)  # 1/delta'_4 = 2^110
        direct = t if direct is None else log2add(direct, t)
    direct = log2add(direct, L.lpin + 8 * L.leps)
    print("T2 = 8@1 5@4 at list 2^40: batch-1 message error 2^%.2f (budget 2^-110), slack by check() %.2f" % (direct, L.check(sizes, first)))
    ok = ok and abs((-110.0 - direct) - L.check(sizes, first)) < 1e-6 and L.check({1: 7, 4: 5}, first) < 0 and L.check({1: 8, 4: 4}, first) < 0
    # the ladder at level 0, list 2^40: recomputed directly, and minimal (one point fewer at any round breaks the budget)
    for kappa, ell, lam in ((24, 6, 40), (24, 6, 100), (24, 6, 300), (20, 4, 40), (20, 4, 300), (4, 4, 100)):
        L = Level(kappa, ell, lam)
        lsz, lslack = ladder(L)
        cum, c, direct = [], 0, L.lpin + lsz[1] * L.leps
        for j in range(1, ell + 1):
            c += lsz.get(j, 0)
            cum.append(c)
            direct = log2add(direct, L.lc1 + c * L.leps + (j - 1) * 119.0)
        minimal = True
        for j in range(ell):
            if cum[j] - 1 < (cum[j - 1] if j else 1):
                continue
            d2 = L.lpin + (cum[0] - (1 if j == 0 else 0)) * L.leps
            for i in range(ell):
                d2 = log2add(d2, L.lc1 + (cum[i] - (1 if i == j else 0)) * L.leps + i * 119.0)
            minimal = minimal and d2 > -110.0
        print("ladder kappa %d ell %d list 2^%d: cumulative %s, message error 2^%.2f (budget 2^-110), no single point can be removed or delayed: %s" % (
            kappa, ell, lam, cum, direct, minimal))
        ok = ok and direct <= -110.0 and minimal and cum[-1] <= single(L)[0][1]
        if (kappa, ell, lam) == (24, 6, 40):
            ok = ok and cum == [6, 7, 8, 10, 11, 12]
    print("selftest", "passed" if ok else "FAILED")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        selftest()
        sys.exit(0)
    for c1 in ("d4", "pair"):
        table(24, 6, (40, 100, 300), c1, True)
        table(20, 4, (40, 100, 300), c1, False)
        table(4, 4, (40, 100, 300), c1, False)
    print("\n### whole opening, mu = 30")
    for c1 in ("d4", "pair"):
        for lam in (40, 100, 300):
            opening(lam, c1)
