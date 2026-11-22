"""Note 83, Section 5: flattening ranks (product structure) of a voted list found by 83_votes, for the whole list and for
a sub-list, at every level. Usage: 83_scales.py file line_index members(e.g. 135)"""
import sys, os, random, importlib.util
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
L83 = load("83_lib"); P = load("83_profile"); V = load("83_verify")
lines = [l for l in open(sys.argv[1]) if "votes:" in l]; line = lines[int(sys.argv[2])]
sub = [int(ch, 36) for ch in sys.argv[3]]
n, t, target, cls = V.expand(line); v = (n // 2).bit_length() - 1; k = n // 2; rnd = random.Random(99)
tw = L83.make_tw(v, rnd); G = L83.gen(tw, v)
ker = L83.kernel(np.array(L83.rows_of(G, k, t, cls)), (t - 1) * k); pt = L83.random_point(ker, rnd)
print("n", n, "members", t, "kernel", len(ker))
print("flattening ranks of the whole list at levels 1..%d:" % v, [P.flat_rank(pt, range(t), 0, k, lev) for lev in range(1, v + 1)])
print("flattening ranks of the sub-list", sub, ":", [P.flat_rank(pt, sub, sub[0], k, lev) for lev in range(1, v + 1)])
