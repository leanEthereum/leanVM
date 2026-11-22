"""Note 76: best split/merge scheme against the exact rank on random three-member patterns at (8,16) (GF(2^64), T2)."""
import random, os, importlib.util, sys, itertools, functools
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
exec(open(os.path.join(here, "76_scheme.py")).read().split("here = os.path")[0])   # join, dim, r
mt = load("76_match"); du = load("76_dual")
rnd = random.Random(1234)
v = 3; n = 16; k = 8; t = 3
tw = du.make_tw(v, 1, rnd); G = [du.row(tw, v, j) for j in range(n)]
tot = bad = dep = 0
for dens in (0.55, 0.65, 0.75):
    for _ in range(100):
        cls = [sum((rnd.random() < dens) << l for l in range(t)) for _ in range(n)]
        rk, w = mt.inc_rank(G, k, t, cls)
        state = tuple(() if bin(c).count("1") < 2 else (frozenset(l for l in range(t) if (c >> l) & 1),) for c in cls)
        val = r(state); tot += 1; dep += rk < w; bad += val != rk
        if val > rk: print("VIOLATION", cls)
print(f"(8,16), three members: random patterns {tot}, rows dependent {dep}, best scheme different from the rank: {bad}")
