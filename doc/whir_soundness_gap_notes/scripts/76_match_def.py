"""Note 76: the matching bound (Corollary 4.2) and the sibling bound (Corollary 4.3) on the deficient orbits of notes 69
and 74 at rate 1/2 (files with lines 'w=.. ranks U=.. 2=.. | classes'). The file gives the exact rank '2=' of the tree code."""
import sys, os, re, importlib.util
import numpy as np
from scipy.optimize import linear_sum_assignment
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("m", os.path.join(here, "76_match.py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
for fn, t in [("69_t2_def_4_8_3_full.txt", 3), ("69_t2_def_8_16_3.txt", 3), ("74_def_4_8_4.txt", 4)]:
    tot = viol = eqm = eqs = nosib = 0
    for line in open(os.path.join(here, fn)):
        head, pat = line.split("|"); w = int(re.search(r"w=(\d+)", head).group(1)); rk = int(re.search(r" 2=(\d+)", head).group(1))
        cls = [0 if c == "." else sum(1 << int(ch) for ch in c) for c in pat.split()]
        n = len(cls); k = n // 2
        W = np.array([[m.dim_union(cls[x], cls[k + y], t) for y in range(k)] for x in range(k)])
        ri, ci = linear_sum_assignment(-W); mb = int(W[ri, ci].sum())
        sb = sum(m.dim_union(cls[2 * p], cls[2 * p + 1], t) for p in range(n // 2))
        tot += 1; viol += (rk < mb) or (rk < sb); eqm += rk == mb; eqs += rk == sb; nosib += sb == w
    print(f"{fn}: patterns {tot}, rank below a bound: {viol}, rank = matching bound: {eqm}, rank = sibling bound: {eqs}, patterns with no sibling overlap (must be 0 among deficient ones): {nosib}")
