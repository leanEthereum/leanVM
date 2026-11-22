"""Cross-check 02_ct32.c against a direct python enumeration for small T (n = 32)."""
import sys, os, subprocess, itertools, random, importlib.util
from collections import Counter
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
binary = sys.argv[1]
F = gf.GF(64)
rng = random.Random(7)
for basis in (gf.power_basis(F, 5), gf.random_basis(F, 5, rng)):
    pts = gf.span(basis)
    for T in (3, 4, 5):
        keys = []
        for S in itertools.combinations(pts, T):
            loc = F.locator(S)  # low first; e_j = loc[T-j]
            keys.append(tuple(loc[T - j] for j in range(1, T)))
        mine = []
        for t in range(1, T):
            cnt = Counter(k[:t] for k in keys)
            mx = max(cnt.values())
            mine.append(f"{mx}({sum(1 for v in cnt.values() if v == mx)})")
        out = subprocess.run([binary, "64", "1b", str(T - 1), "0", str(T)] + [f"{b:x}" for b in basis], capture_output=True, text=True).stdout.split()
        assert out[1:] == mine, (T, out, mine)
        print("ok", T, mine)
