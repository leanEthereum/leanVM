# 59_free_bounds.py: proved upper bound on the free sum of t Reed-Solomon codewords with Hamming-ball windows,
# from pair counting only: every pair coincides freely on at most iota = iota_N(k - 1) positions (Harper), so
# sum_x C(c_x, 2) <= C(t, 2) iota, and the free sum sum_x (c_x - 1) is maximized greedily (raising a position
# from c to c + 1 costs c pair-coincidences and gains 1).
from math import comb


def kk_shadow(j, p):
    s = 0
    while j > 0 and p > 0:
        a = p
        while comb(a + 1, p) <= j:
            a += 1
        s += comb(a, p - 1)
        j -= comb(a, p)
        p -= 1
    return s


def min_nbhd(N, m):
    if m == 0:
        return 0
    r, ball = 0, 1
    while r < N and ball + comb(N, r + 1) <= m:
        r += 1
        ball += comb(N, r)
    if r == N:
        return ball
    j, nb = m - ball, ball + comb(N, r + 1)
    if j and r + 2 <= N:
        nb += kk_shadow(j, N - r - 1)
    return nb


def interior(N, f):
    lo, hi = 0, f
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if min_nbhd(N, mid) <= f:
            lo = mid
        else:
            hi = mid - 1
    return lo


def free_bound(n, t, io):
    B, c, tot = comb(t, 2) * io, 1, 0
    while c < t:  # raise all n positions from c to c + 1 while the budget lasts
        m = min(n, B // c)
        tot += m
        B -= m * c
        if m < n:
            break
        c += 1
    return tot


for rho in (0.5, 0.25):
    for N in (4, 5, 6, 7, 8, 9, 10):
        n = 1 << N
        k = int(rho * n)
        io = interior(N, k - 1)
        print(f"rate {rho} N={N} k={k} iota={io}: " +
              "; ".join(f"t={t}: {free_bound(n, t, io)} / {(t - 1) * k}" for t in (3, 4, 5, 8, 16)))
