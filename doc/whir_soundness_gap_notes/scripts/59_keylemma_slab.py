# 59_keylemma_slab.py: Key Lemma counterexamples V = g * span(monomials in M_1..M_j), g = Lambda_T(M_0),
# M_i the subspace polynomial of span(b_l : l not in I_i) for a partition I_0, ..., I_j of the directions.
# Usage: python3 59_keylemma_slab.py N m k "a0,a1,..,aj" tau_count "monomials" [sample]
# monomials: semicolon-separated exponent vectors over M_1..M_j, for example "000;100;010;001;110;101".
import random
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
lib = __import__("59_lib")
N, m, k = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
sizes = [int(a) for a in sys.argv[4].split(",")]
tcount = int(sys.argv[5])
monos = [[int(ch) for ch in e] for e in sys.argv[6].split(";")]
sample = int(sys.argv[7]) if len(sys.argv) > 7 else 0
assert sum(sizes) == N
F = lib.GF(m)
n = 1 << N
parts, lo = [], 0
for a in sizes:
    parts.append(set(range(lo, lo + a)))
    lo += a
Ms, degM = [], []
for I in parts:
    vals, d = lib.additive_values(F, [1 << l for l in range(N) if l not in I], N)
    Ms.append(vals)
    degM.append(d)
T = sorted(set(Ms[0]))[:tcount]
g = []
for y in Ms[0]:
    v = 1
    for t in T:
        v = F.mul(v, y ^ t)
    g.append(v)
L = len(monos)
maxdeg = tcount * degM[0] + max(sum(e * d for e, d in zip(mo, degM[1:])) for mo in monos)
assert maxdeg < k, (maxdeg, k)
xs = range(n) if not sample else random.Random(59).sample(range(n), sample)
hist = {}
for x in xs:
    rows = [[0] * (N + 1) for _ in range(L)]
    for c, w in enumerate(lib.window(x, N)):
        if g[w] == 0:
            continue
        for j, mo in enumerate(monos):
            v = g[w]
            for e, Mi in zip(mo, Ms[1:]):
                if e:
                    v = F.mul(v, F.pw(Mi[w], e))
            rows[j][c] = v
    d = L - F.rank(rows)
    hist[d] = hist.get(d, 0) + 1
cnt = sum(hist.values())
delta = sum(d * c for d, c in hist.items()) * n // cnt
print(f"N={N} n={n} k={k} rate={k/n:.4f} L={L} maxdeg={maxdeg} |T|={tcount}/{1 << sizes[0]} windows={cnt} "
      f"Delta_x histogram={dict(sorted(hist.items()))} Delta={'~' if sample else ''}{delta} "
      f"L(k-L)={L * (k - L)} exponent={delta - L * (k - L)}")
