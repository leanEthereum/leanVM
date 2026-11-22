"""Test the conjecture: for a generic domain (random basis in GF(2^64)), two T-subsets S, S' of D share
(e_1, ..., e_t) if and only if n_phi(S) = n_phi(S') mod 2^(a+1) for every linear functional phi on D, where
n_phi(S) = #{s in S : phi(s) = 1} and 2^a <= t < 2^(a+1). (Only-if is proved in the report; if is the conjecture.)

Compares the two partitions of the T-subsets, for every T (N = 4) or T <= Tmax (N = 5).
usage: python3 02_walsh_check.py N [Tmax] [seed]
"""
import sys, os, random, itertools, importlib.util
from collections import defaultdict
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)

N = int(sys.argv[1]) if len(sys.argv) > 1 else 4
n = 1 << N
Tmax = int(sys.argv[2]) if len(sys.argv) > 2 else n - 1
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 5
F = gf.GF(64)
basis = gf.random_basis(F, N, random.Random(seed))
pts = gf.span(basis)  # pts[i] is the point with coordinate vector i
par = [[bin(i & phi).count("1") & 1 for i in range(n)] for phi in range(n)]
ok = True
for T in range(2, Tmax + 1):
    tmax = min(T - 1, 7)
    ekeys, wkeys = [], []
    for S in itertools.combinations(range(n), T):
        e = [0] * tmax
        for i in S:
            s = pts[i]
            for j in range(tmax - 1, 0, -1):
                e[j] ^= F.mul(e[j - 1], s)
            e[0] ^= s
        ekeys.append(tuple(e))
        wkeys.append(tuple(sum(par[phi][i] for i in S) for phi in range(1, n)))
    line = []
    for t in range(1, tmax + 1):
        a = t.bit_length() - 1
        mod = 1 << (a + 1)
        m1, m2 = {}, {}
        same = True
        for ek, wk in zip(ekeys, wkeys):
            k1 = ek[:t]
            k2 = tuple(v % mod for v in wk)
            if m1.setdefault(k1, k2) != k2 or m2.setdefault(k2, k1) != k1:
                same = False
                break
        ok &= same
        line.append(f"t={t}:{'same' if same else 'DIFFERENT'}({len(m1)})")
    print(f"N={N} T={T}: " + " ".join(line), flush=True)
print("conjecture holds on all tested (T, t)" if ok else "conjecture FAILS somewhere")
