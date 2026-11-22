# Researcher 12. Differences inside a class at n = 64 (modulus 8 on n_phi), from a member dump of 12_class seed64.
# For every member S != S0 it writes 1_S0 - 1_S = (1/4) sum c_phi chi_phi and prints the histogram of
# (sum c^2, number of characters, rank of their span, multiset of |c|). Checks Proposition 5.1 of note 12:
# |S0 ^ S| is in {n/4, 3n/8, n/2, 5n/8, 3n/4} and S0 ^ S is the support of a quadratic function of rank <= 4.
# usage: python3 12_class_atoms.py members.txt hexseed
import sys
from collections import Counter
N = 6; n = 64
def wht(v):
    v = v[:]; h = 1
    while h < n:
        for i in range(0, n, 2 * h):
            for j in range(i, i + h):
                a, b = v[j], v[j + h]; v[j] = a + b; v[j + h] = a - b
        h *= 2
    return v
def ind(m): return [(m >> x) & 1 for x in range(n)]
def rank(vs):
    b = []
    for v in vs:
        for w in b: v = min(v, v ^ w)
        if v: b.append(v)
    return len(b)
mem = [int(l, 16) for l in open(sys.argv[1])]
s0 = int(sys.argv[2], 16); u = n // 16
st = Counter(); bad = 0
for m in mem:
    if m == s0: continue
    f = [a - b for a, b in zip(ind(s0), ind(m))]
    F = wht(f); assert all(x % (4 * u) == 0 for x in F)
    c = [x // (4 * u) for x in F]; supp = [p for p in range(n) if c[p]]
    X = wht(ind(s0 ^ m)); W = [n - 2 * X[0]] + [-2 * x for x in X[1:]]   # Walsh transform of (-1)^{1_X}
    nz = [p for p in range(n) if W[p]]
    mags = set(abs(W[p]) for p in nz)
    # quadratic of rank 2h: |W| = n / 2^h on an affine space of dimension 2h
    ok = len(mags) == 1 and len(nz) in (1, 4, 16) and list(mags)[0] ** 2 * len(nz) == n * n and rank([p ^ nz[0] for p in nz]) in (0, 2, 4)
    bad += not ok
    st[(sum(x * x for x in c), len(supp), rank(supp), tuple(sorted(Counter(abs(x) for x in c if x).items())))] += 1
print("members", len(mem), "differences that are not quadrics of rank <= 4:", bad)
for k, v in sorted(st.items()): print(k, v)
