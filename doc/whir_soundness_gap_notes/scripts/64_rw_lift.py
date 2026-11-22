"""Note 64, random windows (c): do the structured plain Reed-Solomon triples (periodic lifts of flats triples, the ones
that break local windows in 64_item2_local.py) keep free agreements under random windows?  N = 6, GF(2^8).
For each d: 20 sampled graphs and mu; free pair agreements = interiors of the three zero sets for the random windows;
u_2 + 2 u_3 for the best word. Prediction for a set Z independent of the graph: |int Z| ~ |Z| (|Z|/n)^d."""
import importlib.util, os, random, sys
here = os.path.dirname(__file__)
def load(name, f):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, f))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
L, R, I2 = load("lib64", "64_lib.py"), load("rw", "64_rw_lib.py"), load("item2", "64_item2_local.py")
F, N, n, rng = I2.F, 6, 64, random.Random(66)
LW = L.vanishing(F, [0, 1, 2, 3])
Dq = sorted({I2.peval(LW, v) for v in range(n)})
for k, c, target in ((16, 0, 9), (32, 3, 18)):
    Q1, Q2, cq = I2.find_quotient_triple(Dq, k // 4, c, target)
    P1, P2 = I2.compose(Q1, LW), I2.compose(Q2, LW)
    pw = L.powers(F, n, k)
    e1 = L.evaluate(F, pw, P1 + [0] * (k - len(P1))); e2 = L.evaluate(F, pw, P2 + [0] * (k - len(P2)))
    e12 = [a ^ b for a, b in zip(e1, e2)]
    Zs = [[v for v in range(n) if e[v] == 0] for e in (e1, e2, e12)]
    print(f"k={k}: lifted triple, pointwise u_2+2u_3 = {I2.count3(e1, e2)} against 2k = {2*k}; zero-set sizes {[len(Z) for Z in Zs]}")
    for d in (2, 4, 6, 8):
        fr, sc = [], []
        for _ in range(20):
            win = R.rand_windows(n, d, rng)
            mu = [[F.rand(rng) for _ in range(d)] for _ in range(n)]
            fr.append(sum(len(R.interior_w(Z, win)) for Z in Zs))
            sc.append(I2.count3(R.mix_w(F, mu, e1, win), R.mix_w(F, mu, e2, win)))
        pred = sum(len(Z) * ((len(Z) - 1) / (n - 1)) ** d for Z in Zs)
        print(f"   d={d}: total free pair agreements mean {sum(fr)/20:.2f} max {max(fr)} (prediction {pred:.2f});"
              f" u_2+2u_3 mean {sum(sc)/20:.2f} max {max(sc)}")
