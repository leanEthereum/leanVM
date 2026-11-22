"""Note 76: is the best split/merge scheme of Theorem 4.1 equal to the exact rank? Random patterns at (4,8), GF(2^64), T2."""
import random, os, importlib.util, sys
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
sc = load("76_scheme") if False else None
import itertools, functools
exec(open(os.path.join(here, "76_scheme.py")).read().split("here = os.path")[0])   # join, dim, r
mt = load("76_match"); du = load("76_dual")
rnd = random.Random(99)
v = 2; n = 8; k = 4
tw = du.make_tw(v, 1, rnd); G = [du.row(tw, v, j) for j in range(n)]
for t, dens, trials in [(3, 0.6, 3000), (4, 0.6, 3000), (5, 0.6, 2000), (6, 0.6, 1500), (8, 0.6, 800), (8, 0.75, 800), (12, 0.6, 300)]:
    bad = 0; dep = 0; ex = None
    for _ in range(trials):
        cls = [sum((rnd.random() < dens) << l for l in range(t)) for _ in range(n)]
        rk, w = mt.inc_rank(G, k, t, cls)
        state = tuple(() if bin(c).count("1") < 2 else (frozenset(l for l in range(t) if (c >> l) & 1),) for c in cls)
        val = r(state)
        if val > rk: print("VIOLATION", cls, rk, val)
        dep += rk < w
        if val != rk:
            bad += 1
            if ex is None: ex = (cls, rk, val)
    print(f"members {t} density {dens}: patterns {trials}, rows dependent {dep}, scheme bound below the rank: {bad}", ("first: classes %s rank %d bound %d" % ([format(c, 'b') for c in ex[0]], ex[1], ex[2])) if ex else "")
    sys.stdout.flush()
