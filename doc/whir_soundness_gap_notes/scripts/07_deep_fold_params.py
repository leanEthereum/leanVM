#!/usr/bin/env python3
"""Numbers for note 07: the mu = 30 ladder, what the DEEP fold affords, and what it would buy.

Pure python, instant. Model:
  - ladder of `derive_config` at log_n = 30: folds [6,4,4,4,4,4], kappa = [24,20,16,12,8,4], rate exponents
    R + [0,3,6,9,12,15], n_i = 2^(kappa_i + R_i), analysis degree d_i = 2^kappa_i - 1 + fold_i;
  - a level at threshold A takes t = ceil(108 / log2(n / (A - 1))) queries (125 bits, 17-bit query grind);
  - bytes of a level's queries: t * (leaf + 32 * (depth - floor(log2 t))), leaf = 64 K words (512 B) at level 0
    and 16 E values (256 B) after: a rough stand-in for the pruned paths (note 08 has the validated model);
  - DEEP fold (note 07, section 3): with s points per fold round, bad points have probability at most
    4 Lambda^3 q^6 eps^s / K0^3 with eps = (d + 2 + log2 lanes) / q, and the fold challenge errs with K0 / q^2.
"""
import math

LOG_Q = 128
FOLDS = [6, 4, 4, 4, 4, 4]
KAPPA = [24, 20, 16, 12, 8, 4]
RATE_STEP = [0, 3, 6, 9, 12, 15]
DEPLOYED = {1: [218, 55, 32, 23, 18, 15], 2: [109, 44, 28, 21, 17, 15], 3: [73, 37, 25, 19, 16, 15], 4: [55, 32, 23, 18, 16, 14]}
QUERY_BITS = 125 - 17


def level(r0, i):
    kappa, fold, r = KAPPA[i], FOLDS[i], r0 + RATE_STEP[i]
    n = 1 << (kappa + r)
    d = (1 << kappa) - 1 + fold
    return kappa, fold, r, n, d


def queries(bits_per_query):
    return math.ceil(QUERY_BITS / bits_per_query - 1e-12)


def level_bytes(i, t, n):
    leaf = 512 if i == 0 else 256
    depth = int(math.log2(n))
    return t * (leaf + 32 * max(0, depth - int(math.log2(max(t, 1)))))


def johnson_table():
    print("== 1. Queries: the formula against the deployed table (Johnson threshold A = isqrt(n d) + 1 + fold)")
    print("rate level kappa R  n      bits/query(Johnson)  t(formula)  deployed  bits/query(capacity)  t(capacity)")
    for r0 in (1, 2, 3, 4):
        total_dep = total_cap = 0
        for i in range(6):
            kappa, fold, r, n, d = level(r0, i)
            a = math.isqrt(n * d) + 1 + fold
            bj = math.log2(n / (a - 1))
            bc = math.log2(n / (d + 1))
            tj, tc = queries(bj), queries(bc)
            total_dep += level_bytes(i, DEPLOYED[r0][i], n)
            total_cap += level_bytes(i, tc, n)
            print(f"1/{1 << r0:<3} L{i}    {kappa:<5} {r:<2} 2^{kappa + r:<3} {bj:<20.4f} {tj:<11} {DEPLOYED[r0][i]:<9} {bc:<21.4f} {tc}")
        print(f"      query bytes: deployed about {total_dep / 1024:.0f} KiB, every level at capacity about {total_cap / 1024:.0f} KiB")


def deep_budget():
    print("\n== 2. DEEP fold: largest log2(list) per level, by the number s of points per fold round")
    print("   bad points <= 4 L^3 q^6 eps^s / K0^3 <= 2^-119 with K0 = 2^9 q (fold error 2^-119, the present 7-bit grind)")
    print("level kappa log2(eps)   s=4     s=5     s=6     s=7     s=8     s=10    s=12")
    for i in range(6):
        kappa, fold, r, n, d = level(1, i)
        log_eps = math.log2(d + 2 + fold) - LOG_Q
        row = []
        for s in (4, 5, 6, 7, 8, 10, 12):
            # 4 L^3 q^3 eps^s / 2^27 <= 2^-119
            row.append((-119 + 25 - 384 - s * log_eps) / 3)
        print(f"L{i}    {kappa:<5} {log_eps:<10.1f} " + " ".join(f"{max(x, float('-inf')):7.1f}" if x > 0 else "      -" for x in row))
    print("   each extra bit of fold grinding adds 4/3 bit to log2(list); commit-time separation C(L,2) eps^s q is slacker")


def deep_cost():
    print("\n== 3. DEEP fold: extra proof bytes at mu = 30 (26 fold rounds), 16-byte scalars")
    rounds = sum(FOLDS)
    for s in (5, 6, 7, 8):
        v1 = rounds * 2 * s * 16
        v2 = rounds * 3 * s * 16
        print(f"s = {s}: answers only (extra lambda message per round) {v1 / 1024:.1f} KiB; one-round persistence {v2 / 1024:.1f} KiB")
    print(f"today the fold rounds send {rounds * 4 * 16 / 1024:.1f} KiB")


def what_if():
    print("\n== 4. What a list bound would buy at level 0 (n = 2^(24+R)); frontier families from note 01, table of section 4")
    cases = {
        1: [("Johnson, no slack", 2 ** -0.5, None), ("0.6318 (lists 2^10 by biased padding stop here)", 0.6318, 10), ("5/8 (trees, 2^29.4)", 0.625, 29.4), ("9/16 (trees, 2^102.7)", 0.5625, 102.7), ("capacity", 0.5, None)],
        2: [("Johnson = flats (2^26)", 0.5, 26), ("3/8 (2^27.8, Gold 2^30.5..34.5)", 0.375, 34.5), ("5/16 (2^47.4)", 0.3125, 47.4), ("capacity", 0.25, None)],
        3: [("Johnson", 2 ** -1.5, None), ("1/4 (flats, 2^49.4)", 0.25, 49.4), ("capacity", 0.125, None)],
        4: [("Johnson", 0.25, None), ("1/8 (flats, 2^70.6)", 0.125, 70.6), ("capacity", 0.0625, None)],
    }
    for r0, rows in cases.items():
        kappa, fold, r, n, d = level(r0, 0)
        print(f"rate 1/{1 << r0}: deployed t = {DEPLOYED[r0][0]}")
        for name, tau, fam in rows:
            t = queries(-math.log2(tau)) if tau > 2 ** -r0 else queries(math.log2(n / (d + 1)))
            saved = level_bytes(0, DEPLOYED[r0][0], n) - level_bytes(0, t, n)
            note = "" if fam is None else f"; known family of 2^{fam:.1f} at this agreement"
            print(f"   T/n -> {name:<48} t = {t:<4} level-0 bytes saved about {saved / 1024:6.1f} KiB{note}")


def last_level():
    print("\n== 5. Last levels: the counting bound Lambda(T) <= C(n, d+1) / C(T, d+1) with the DEEP fold")
    for i in (5, 4):
        kappa, fold, r, n, d = level(1, i)
        dd = d + 1  # degree bound d, so d + 1 agreement points fix a member
        log_eps = math.log2(d + 2 + fold) - LOG_Q
        print(f"L{i}: kappa = {kappa}, n = 2^{kappa + r}, d = {d}, deployed t = {DEPLOYED[1][i]}")
        for b in (r / 2, 0.625 * r, 0.75 * r, 0.875 * r, r - 1.2):
            t_agree = n / 2**b
            if t_agree <= dd + fold + 1:
                continue
            log_list = (math.lgamma(n + 1) - math.lgamma(n - dd + 1) - math.lgamma(t_agree + 1) + math.lgamma(t_agree - dd + 1)) / math.log(2)
            s = math.ceil((3 * log_list + 474 + 120 * (fold - 1)) / -log_eps)
            t = queries(b)
            extra = (fold + 1) * s * 16
            saved = level_bytes(i, DEPLOYED[1][i], n) - level_bytes(i, t, n)
            print(f"   bits/query {b:5.2f}: log2 list <= {log_list:7.1f}, s = {s:3d} points, variant P ({extra / 1024:.1f} KiB), t = {t:2d}, query bytes saved {saved / 1024:.1f} KiB")


def grinding():
    print("\n== 6. Queries saved per extra bit of query grinding (Johnson thresholds), and bytes")
    for r0 in (1, 2, 3, 4):
        row = []
        for i in range(6):
            kappa, fold, r, n, d = level(r0, i)
            a = math.isqrt(n * d) + 1 + fold
            bj = math.log2(n / (a - 1))
            per_bit = 1 / bj
            t = DEPLOYED[r0][i]
            marginal = level_bytes(i, t, n) / t
            row.append(f"L{i} {per_bit:4.2f}q/{per_bit * marginal / 1024:4.2f}KiB")
        print(f"rate 1/{1 << r0}: " + "  ".join(row))


def persistent_points():
    print("\n== 2b. Variant P (points fixed per level, carried unbatched): s per level for a list bound 2^b")
    print("   s (-log2 eps) >= 3 b + 474 + 120 (fold - 1): fold error 2^-120, nesting threshold 2^-120, point message 2^-111")
    for b in (8, 40, 70, 100):
        ss = []
        for i in range(6):
            kappa, fold, r, n, d = level(1, i)
            log_eps = math.log2(d + 2 + fold) - LOG_Q
            ss.append(math.ceil((3 * b + 474 + 120 * (fold - 1)) / -log_eps))
        elements = sum(s * (f + 1) for s, f in zip(ss, FOLDS))
        print(f"b = {b:3d}: s = {ss}, scalars sent {elements} ({elements * 16 / 1024:.1f} KiB; today {sum(FOLDS) * 4 + 6} scalars, {(sum(FOLDS) * 4 + 6) * 16 / 1024:.1f} KiB)")


def ladder(mu, r0, k0, red0, k_sub, red_sub, res_max):
    levels = []
    n_run, rate, fold_run, red = mu - k0, r0, k0, red0
    levels.append((n_run, rate, k0))
    while n_run > res_max:
        k = min(k_sub, n_run)
        rate += fold_run - red
        red = red_sub
        levels.append((n_run - k, rate, k))
        n_run -= k
        fold_run = k
    return levels, n_run


def ladders():
    print("\n== 7. Other ladders at mu = 30, rate 1/2, Johnson thresholds without slack (deployed counts are 0 to 2 above)")
    print("   (k0, red0, k, red, residual): queries per level | query KiB + final polynomial KiB | codeword bytes after level 0 / level 0")
    for name, spec in (
        ("deployed", (6, 3, 4, 1, 5)),
        ("level-0 fold 4", (4, 3, 4, 1, 5)),
        ("level-0 fold 5", (5, 3, 4, 1, 5)),
        ("first reduction 2", (6, 2, 4, 1, 5)),
        ("no later reduction", (6, 3, 4, 0, 5)),
        ("fold 5 after level 0", (6, 3, 5, 1, 5)),
        ("residual 2^8 (one level fewer)", (6, 3, 4, 1, 8)),
    ):
        levels, res = ladder(30, 1, *spec)
        ts, total, later = [], 0, 0
        for i, (cols, rate, k) in enumerate(levels):
            n = 1 << (cols + rate)
            d = (1 << cols) - 1 + k
            a = math.isqrt(n * d) + 1 + k
            t = queries(math.log2(n / (a - 1)))
            ts.append(t)
            leaf = (8 if i == 0 else 16) << k
            depth = cols + rate
            total += t * (leaf + 32 * max(0, depth - int(math.log2(t))))
            if i:
                later += (16 << k) * n
        final = ((1 << res) + levels[-1][2]) * 16
        l0 = (8 << levels[0][2]) * (1 << (levels[0][0] + levels[0][1]))
        print(f"   {name:<32} {str(spec):<18} {ts} | {total / 1024:.0f} + {final / 1024:.1f} | {later / l0:.2f}")


if __name__ == "__main__":
    johnson_table()
    deep_budget()
    persistent_points()
    deep_cost()
    what_if()
    last_level()
    grinding()
    ladders()
