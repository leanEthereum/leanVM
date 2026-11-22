# 59_toy_keylemma.py: exact E_V[q^Delta(V)] at k = N + 2 (each I(W_x) is the line spanned by G_x = vanishing
# polynomial of the window of x, so Delta(V) = #{x : G_x in V}). If every L + 1 of the G_x are linearly independent
# then E_V[q^Delta] = sum_{j <= L} C(n, j) (q-1)^j [k-j, L-j]_q / [k, L]_q exactly. Dependencies among the G_x are
# searched exhaustively up to translation (subsets containing x = 0).
import sys
from fractions import Fraction
from itertools import combinations
from math import comb

sys.path.insert(0, __file__.rsplit("/", 1)[0])
lib = __import__("59_lib")


def gauss(q, a, b):
    num = den = 1
    for i in range(b):
        num *= q ** (a - i) - 1
        den *= q ** (i + 1) - 1
    return Fraction(num, den)


for N, m in ((4, 4), (4, 8), (5, 5), (5, 8), (6, 6), (6, 8)):
    F = lib.GF(m)
    n, k, q = 1 << N, N + 2, 1 << m
    G = []
    for x in range(n):
        co = [1]  # coefficients of prod (X + w), low degree first
        for w in lib.window(x, N):
            new = [0] * (len(co) + 1)
            for i, a in enumerate(co):
                new[i + 1] ^= a
                new[i] ^= F.mul(a, w)
            co = new
        G.append(co)
    line = f"N={N} q=2^{m} k={k}:"
    for size in (3, 4, 5):
        if size - 1 > N - 2 or comb(n - 1, size - 1) > 700000:
            continue
        dep = sum(1 for S in combinations(range(1, n), size - 1) if F.rank([G[0]] + [G[y] for y in S]) < size)
        L = size - 1
        e = sum(comb(n, j) * (q - 1) ** j * gauss(q, k - j, L - j) for j in range(L + 1)) / gauss(q, k, L)
        lead = Fraction(n * (q - 1) * (q**L - 1), q**k - 1)
        line += f" dependent {size}-subsets through 0: {dep}; L={L}: E-1={float(e - 1):.4g} (lead {float(lead):.4g});"
    print(line)
