# 59_tables.py: exact recomputation of the tables of note 57 (Sections 2 and 8), the pigeonhole frontier,
# Harper's interior function, and the pair-counting bound on free configurations.
from math import ceil, comb, log2


def H(a):
    return 0.0 if a in (0, 1) else -a * log2(a) - (1 - a) * log2(1 - a)


def bisect(f, lo, hi):
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) >= 0:
            hi = mid
        else:
            lo = mid
    return hi


def a_M(rho, L, N):  # smallest a satisfying inequality (1) of note 57
    n = 2.0**N
    return bisect(lambda a: 64 * ((L + 1) * a - 1 - L * rho) * n - (L + 1) * H(a) * n - 130, rho, 1 - 1e-12)


def queries(a):
    return ceil(108 / log2(1 / a) - 1e-12)


print("Section 2 table, inequality (1), level 0 (N = 24 + R):")
for rho, N, Ls in ((0.5, 25, (1, 2, 3, 4, 5, 7, 10, 15, 23)), (0.25, 26, (2, 3, 7, 15, 24)), (0.125, 27, (3, 15)), (0.0625, 28, (3, 15))):
    pig = bisect(lambda a: a - rho - H(a) / 64, rho, 0.9)
    print(f"  rate {rho}: Johnson {rho**0.5:.4f} ({queries(rho**0.5)} at the radius, {queries(rho**0.5 + 1e-9)} just above), "
          f"pigeonhole rho + H(a)/64 = {pig:.4f} ({queries(pig)})")
    for L in Ls:
        a = a_M(rho, L, N)
        sing = rho + (1 - rho) / (L + 1)
        print(f"    L={L:2d}: a={a:.5f} (Singleton part {sing:.5f}, entropy part {a - sing:.5f}) queries={queries(a)} "
              f"list bound q^{L - 1} = 2^{64 * (L - 1)}")

print("Section 8 thresholds g_t(alpha) = (t-1) rho [+ t H(alpha)/64], g_t(p) = t p - 1 + (1-p)^t:")
for rho in (0.5, 0.25, 0.125, 0.0625):
    row = []
    for t in (3, 4, 5, 8, 16):
        g = lambda p: t * p - 1 + (1 - p) ** t
        a0 = bisect(lambda p: g(p) - (t - 1) * rho, rho, 1)
        a1 = bisect(lambda p: g(p) - (t - 1) * rho - t * H(p) / 64, rho, 1)
        row.append(f"t={t}: {a0:.4f} / {a1:.4f} ({queries(a1)})")
    print(f"  rate {rho}: " + "; ".join(row) + f"; Johnson {rho**0.5:.4f}")


def kk_shadow(j, p):  # least lower shadow of j sets of size p (Kruskal-Katona)
    s = 0
    while j > 0 and p > 0:
        a = p
        while comb(a + 1, p) <= j:
            a += 1
        s += comb(a, p - 1)
        j -= comb(a, p)
        p -= 1
    return s


def min_nbhd(N, m):  # least |T + C| over |T| = m (Harper: initial segments of the simplicial order)
    if m == 0:
        return 0
    r, ball = 0, 1
    while r < N and ball + comb(N, r + 1) <= m:
        r += 1
        ball += comb(N, r)
    j = m - ball
    if r == N:
        return ball
    nb = ball + comb(N, r + 1)
    if j and r + 2 <= N:
        nb += kk_shadow(j, N - r - 1)
    return nb


def interior(N, f):  # largest |T| with |T + C| <= f
    lo, hi = 0, f
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if min_nbhd(N, mid) <= f:
            lo = mid
        else:
            hi = mid - 1
    return lo


def free_bound(n, t, phi_n):  # max sum (c_x - 1) subject to sum C(c_x, 2) <= C(t, 2) phi_n over n positions
    b = comb(t, 2) * phi_n / n
    c = 1
    while c < t and comb(c + 1, 2) <= b:
        c += 1
    return n * ((c - 1) + (b - comb(c, 2)) / c) if c < t else n * (t - 1)


print("Pair counting on free configurations: iota = largest interior of a set of fewer than k points (Harper);")
print("the free t-wise inequality is implied for every t when iota/n <= rho^2; otherwise first t where the bound exceeds (t-1)k:")
for rho in (0.5, 0.25):
    out = []
    for N in list(range(4, 13)) + [16, 20, 25, 26, 28]:
        n = 1 << N
        k = int(rho * n)
        io = interior(N, k - 1)
        bad = next((t for t in range(3, 200) if free_bound(n, t, io) > (t - 1) * k + 1e-9), None)
        out.append(f"N={N}: iota/n={io / n:.4f} first bad t={bad}")
    print(f"  rate {rho} (rho^2 = {rho * rho}): " + "; ".join(out))

print("Check of Harper's function by exhaustion, N = 4 (all subsets):")
N = 4
nb = [0] * 16
for v in range(16):
    nb[v] = (1 << v) | sum(1 << (v ^ (1 << i)) for i in range(N))
best = {}
for T in range(1, 1 << 16):
    cl = 0
    t = T
    while t:
        low = t & -t
        cl |= nb[low.bit_length() - 1]
        t ^= low
    m = bin(T).count("1")
    c = bin(cl).count("1")
    if c < best.get(m, 99):
        best[m] = c
assert all(best[m] == min_nbhd(4, m) for m in best), "Harper mismatch"
print("  ok: min |T + C| =", [best[m] for m in sorted(best)])

print("Rank-one term of the Key Lemma, exact (L = 1): E_V[q^Delta] - 1 = sum over nonempty T with |T + C| < k of")
print("(q-1)^|T| (q^(k-|T+C|) - 1)/(q^k - 1), against the leading term n (q-1)(q^(k-N-1) - 1)/(q^k - 1); N = 4:")
from fractions import Fraction
prof = {}
for T in range(1, 1 << 16):
    cl = 0
    t = T
    while t:
        low = t & -t
        cl |= nb[low.bit_length() - 1]
        t ^= low
    key = (bin(T).count("1"), bin(cl).count("1"))
    prof[key] = prof.get(key, 0) + 1
for q in (16, 2**64):
    for k in (6, 7, 8):
        e = sum(Fraction(cnt * (q - 1) ** a * (q ** (k - b) - 1), q**k - 1) for (a, b), cnt in prof.items() if b < k)
        lead = Fraction(16 * (q - 1) * (q ** (k - 5) - 1), q**k - 1)
        print(f"  q=2^{int(log2(q))} k={k}: E-1 = {float(e):.6g}, leading term {float(lead):.6g}, ratio {float(e / lead):.6f}")
