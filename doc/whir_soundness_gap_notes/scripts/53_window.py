#!/usr/bin/env python3
"""53_window.py: exact integers used in 53-goppa-structure-degenerate.md (Sections 2.4, 4, 6).

Rate 1/2, Delta = n/2 + 5, A = ceil(a n): the window of note 48 for contact 4 on all lines, the bound s on
deg r_P, the lower bounds on the degree of the Goppa divisor (clean; pair divisor with r), the weight range of
S_i xor S_j, and the second-moment bound M <= (1 - c) / ((2a - 1)^2 - c), c = 1 - 2 w_1 / n, for a code whose words
of weight >= 2(A - Delta) all have weight >= w_1 (RM(2, N): w_1 = 7n/16; RM(1, N): w_1 = n/2). All in exact
rational arithmetic.

Run: python3 53_window.py
"""
from fractions import Fraction as Fr


def second_moment(n, A, w1):
    """largest M with M ((2A - n)^2 - n (n - 2 w1)) <= n^2 - n (n - 2 w1), or None."""
    c_n = n - 2 * w1                       # c n
    den = (2 * A - n) ** 2 - n * c_n       # ((2a-1)^2 - c) n^2
    num = n * n - n * c_n                  # (1 - c) n^2
    return None if den <= 0 else num // den


def main():
    print("# rate 1/2, contact 4 on all lines; window [Delta + 3A, W_cut), W_cut from notes 45 and 48 (in units of n)")
    for lg in (25, 28):
        n = 1 << lg
        Delta = n // 2 + 5
        for (a_num, a_den, wcut) in ((7065, 10000, Fr(26352, 10000)), (705, 1000, Fr(26498, 10000))):
            A = -(-a_num * n // a_den)
            Wlo = Delta + 3 * A
            Wcut = int(wcut * n)
            s = Wcut - Delta - 3 * A
            clean = A - Delta + 1
            pair = A - Delta - 5 * s
            cls = A - Delta - 3 * s
            print(f"  n = 2^{lg}, a = {a_num}/{a_den}: A = {A}, W in [{Wlo / n:.4f}, {float(wcut):.4f}) n, s = deg r_P <= {s} "
                  f"({s / n:.4f} n)")
            print(f"     deg of the divisor: clean >= A - Delta + [p_inf > Delta] ~ {clean} ({clean / n:.4f} n); "
                  f"pair divisor >= A - Delta - 5 s = {pair} ({pair / n:.4f} n); within one class of r: >= {cls} "
                  f"({cls / n:.4f} n); Pade uniqueness needs 2 s = {2 * s} below it: {2 * s < cls}")
            lo, hi = 2 * (A - Delta), 2 * (n - A)
            bad_hi = Fr(2 * A * (n - A), n)
            print(f"     |S_i xor S_j| in [{lo}, {hi}] = [{lo / n:.4f}, {hi / n:.4f}] n; the second-moment argument needs no "
                  f"codeword of weight in [{lo / n:.5f}, {float(bad_hi) / n:.5f}] n (width {float(bad_hi - lo) / n:.5f} n)")
            # with the factors r_P: the sets O_P = (odd roots of eps_P in D), |O_P| >= A - s, pairwise distances
            # >= 2(A - Delta) - 2s; if all odd roots of the r_P lie in D the differences are codewords
            Ap = A - s
            dmin = 2 * (A - Delta) - 2 * s
            print(f"     with r_P (odd roots in D): |O_P| >= A - s = {Ap} ({Ap / n:.4f} n), distances >= {dmin / n:.4f} n "
                  f"(> 3n/8: {dmin > 3 * n // 8}); second moment with w_1 = 7n/16: M <= {second_moment(n, Ap, 7 * n // 16)}; "
                  f"with w_1 = n/2: M <= {second_moment(n, Ap, n // 2)}")
            for (name, w1) in (("RM(2,N), w_1 = 7n/16", 7 * n // 16), ("RM(1,N), w_1 = n/2", n // 2),
                               ("w_1 = 27n/64", 27 * n // 64), ("w_1 = 55n/128", 55 * n // 128)):
                print(f"        {name}: M <= {second_moment(n, A, w1)}")
    print("# thresholds of Theorem S (note 52), second-moment bound with RM(2, N) at rate 1/2")
    n = 1 << 25
    for a6 in (700840, 701000, 703000, 705000, 706500, 707000):
        A = -(-a6 * n // 10 ** 6)
        Delta = n // 2 + 5
        lo = 2 * (A - Delta)
        ok = lo > 3 * n // 8
        print(f"  a = {a6 / 1e6:.6f}: 2(A - Delta) = {lo / n:.4f} n > 3n/8: {ok}; M <= {second_moment(n, A, 7 * n // 16)}")
    print("# other rates (equal sizes w = A, pairwise distance >= d): Johnson M <= (d/2) / (d/2 - w (n - w) / n)")
    for (name, rho, a6) in (("1/4", Fr(1, 4), 488109), ("1/8", Fr(1, 8), 340086), ("1/16", Fr(1, 16), 237478)):
        A = -(-a6 * n // 10 ** 6)
        Delta = int(rho * n) + 5
        lo = 2 * (A - Delta)
        # RM(2,N) weights n/2 - n/2^(h+1): the smallest one >= lo
        h = 1
        while n // 2 - (n >> (h + 1)) < lo:
            h += 1
        w1 = n // 2 - (n >> (h + 1))
        den = Fr(w1, 2) - Fr(A * (n - A), n)
        M = None if den <= 0 else int(Fr(w1, 2) / den)
        print(f"  rate {name}, a = {a6 / 1e6}: g = A - Delta - 1 = {(A - Delta - 1) / n:.4f} n (RM(2,N) needs >= 1/8, RM(1,N) "
              f">= 1/4); 2(A - Delta) = {lo / n:.4f} n; next RM(2,N) weight {w1 / n:.5f} n; Johnson bound: {M}")


if __name__ == "__main__":
    main()
