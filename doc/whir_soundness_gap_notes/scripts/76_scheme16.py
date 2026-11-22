"""Note 76: the best split/merge scheme (Theorem 4.1) on the deficient three-member orbits at (8,16) of note 69
for which the matching bound of Corollary 4.2 is not already equal to the rank."""
import os, re, sys, itertools, functools, importlib.util
import numpy as np
from scipy.optimize import linear_sum_assignment
here = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(here, "76_scheme.py")).read().split("here = os.path")[0])   # join, dim, r
spec = importlib.util.spec_from_file_location("m", os.path.join(here, "76_match.py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
tot = eq = sel = 0
for line in open(os.path.join(here, "69_t2_def_8_16_3.txt")):
    head, pat = line.split("|"); rk = int(re.search(r" 2=(\d+)", head).group(1))
    cl = pat.split(); cls = [0 if c == "." else sum(1 << int(ch) for ch in c) for c in cl]
    W = np.array([[m.dim_union(cls[x], cls[8 + y], 3) for y in range(8)] for x in range(8)])
    ri, ci = linear_sum_assignment(-W); mb = int(W[ri, ci].sum())
    tot += 1
    if mb == rk: continue
    sel += 1
    state = tuple(() if c == "." or len(c) < 2 else (frozenset(int(ch) for ch in c),) for c in cl)
    val = r(state); eq += val == rk
    if val > rk: print("VIOLATION", line)
    if val != rk and sel - eq <= 5: print("not exact:", pat.strip(), "rank", rk, "matching bound", mb, "best scheme", val); sys.stdout.flush()
print(f"orbits {tot}, matching bound below the rank: {sel}, of which the best scheme equals the rank: {eq}")
