"""List-size profiles of structured words, through the exhaustive oracle 02_lists (profile mode).

usage: python3 02_words.py <binary> N k Tmin [power|random:<seed>]
Words tried: monomials x^j, pole words x^j/(x - beta) with beta outside D, 1/(L_V(x) - c) for subspaces V,
and a random word. Prints, per word, the number of polynomials of degree < k at each agreement >= Tmin.
"""
import sys, os, subprocess, random, importlib.util
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)

binary, N, k, Tmin = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mode = sys.argv[5] if len(sys.argv) > 5 else "power"
F = gf.GF(64)
rng = random.Random(3)
basis = gf.power_basis(F, N) if mode == "power" else gf.random_basis(F, N, random.Random(int(mode.split(":")[1])))
D = gf.span(basis)
n = len(D)
beta = (1 << N) if mode == "power" else F.rand(rng)
words = []
for j in range(k, n):
    words.append((f"x^{j}", [F.pow(x, j) for x in D]))
ib = [F.inv(x ^ beta) for x in D]
for j in range(0, n):
    words.append((f"x^{j}/(x-beta)", [F.mul(F.pow(x, j), i) for x, i in zip(D, ib)]))
for s in range(1, N):
    c = gf.subspace_poly(F, basis[:s])
    cc = F.rand(rng)
    words.append((f"1/(L_V-c) dimV={s}", [F.inv(gf.lin_eval(F, c, x) ^ cc) for x in D]))
    words.append((f"1/L_V off V, 0 on V, dimV={s}", [F.inv(v) if (v := gf.lin_eval(F, c, x)) else 0 for x in D]))
words.append(("1/x, 0 at 0", [F.inv(x) if x else 0 for x in D]))
words.append(("random", [F.rand(rng) for _ in D]))
inp = " ".join(f"{x:x}" for x in D) + "\n" + "\n".join(" ".join(f"{v:x}" for v in w) for _, w in words) + "\n"
out = subprocess.run([binary, "profile", "64", "1b", str(n), str(k), str(Tmin)], input=inp, capture_output=True, text=True).stdout.splitlines()
print(f"# N={N} n={n} k={k} D={mode}: polynomials of degree < k by exact agreement (>= {Tmin})")
for (name, _), line in zip(words, out):
    if line.strip():
        print(f"{name:32s} {line}")
