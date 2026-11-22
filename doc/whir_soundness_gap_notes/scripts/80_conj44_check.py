#!/usr/bin/python3
# Referee 80: a counterexample to note 76's Conjecture 4.4, evaluated with note 76's OWN recursion r (76_scheme.py) and its own
# exact rank (76_match.inc_rank, 76_dual tree code, GF(2^64), T2), for several draws of the twiddles.
# usage: 80_conj44_check.py "<16 or 32 leaf types 0..4>" ...   (types: 0 none, 1 = {0,1}, 2 = {0,2}, 3 = {1,2}, 4 = {0,1,2})
import random, os, importlib.util, sys, itertools, functools
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
exec(open(os.path.join(here, "76_scheme.py")).read().split("here = os.path")[0])   # join, dim, r  (note 76's definitions)
mt = load("76_match"); du = load("76_dual")
CLS = {0: 0, 1: 3, 2: 5, 3: 6, 4: 7}
pats = sys.argv[1:] or ["2 2 4 4 0 0 0 4 0 4 4 0 3 3 1 1"]
for ps in pats:
    types = [int(c) for c in ps.split()]
    n = len(types); k = n // 2; v = k.bit_length() - 1; t = 3
    cls = [CLS[c] for c in types]
    w = sum(max(bin(c).count("1") - 1, 0) for c in cls)
    ranks = []
    for seed in (11, 22, 33):
        rnd = random.Random(seed)
        tw = du.make_tw(v, 1, rnd); G = [du.row(tw, v, j) for j in range(n)]
        rk, w2 = mt.inc_rank(G, k, t, cls); ranks.append(rk); assert w2 == w
    state = tuple(() if bin(c).count("1") < 2 else (frozenset(l for l in range(t) if (c >> l) & 1),) for c in cls)
    val = r(state) if n <= 16 else None
    print(f"pattern {ps}: weight {w}, Lk = {2 * k}, exact rank (note 76's code, three draws) {ranks}, note 76's recursion r_v = {val}")
