#!/usr/bin/python3
# Referee 87: independent recomputation of the thresholds of note 84, Theorem 8.2, column J = 0
# (nothing checked): eps_t from 87_eps.py at p_t = 2^-140, then the linear program with slack
#   maximize E[theta]  s.t.  E[h_j(theta)] <= j rho + eps_{j+1},  h_j = Pr[Bin(j+1, theta) >= 2],
# grid primal (lower estimate) and a dual certificate checked on a fine grid with a Lipschitz margin.
import math, sys, importlib.util, os
import numpy as np
from scipy.optimize import linprog

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("eps87", os.path.join(here, "87_eps.py"))
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)

def h(j, th):
    return 1.0 - (1.0 - th) ** (j + 1) - (j + 1) * th * (1.0 - th) ** j

def constraint_set(r):
    rho = 2.0 ** -r
    js = list(range(1, 49))
    j = 49.0
    while j < 1.0 / rho:
        if int(j) > js[-1]:
            js.append(int(j))
        j *= 1.04
    return js

def run(r, lgn, J=0, slack=True):
    rho = 2.0 ** -r
    v = lgn - r
    js, b = [], []
    for j in constraint_set(r):
        if slack:
            # two-stage search for lambda: coarse then step 0.05 around the coarse optimum
            e0, lam0, _, _ = E.best(r, v, J, 140, j + 1, step=1.0, lo=0.05, hi=40.0)
            e, lam, _, _ = E.best(r, v, J, 140, j + 1, step=0.05, lo=max(0.05, lam0 - 1.0), hi=lam0 + 1.0)
            e = min(e, e0)
        else:
            e = 0.0
        rhs = j * rho + e
        if rhs < 1.0:
            js.append(j)
            b.append(rhs)
    # grid: uniform and geometric points
    th = np.unique(np.concatenate([np.linspace(0, 1, 4001), np.geomspace(1e-6, 1, 6000)]))
    A = np.array([h(j, th) for j in js])
    res = linprog(-th, A_ub=A, b_ub=np.array(b), A_eq=np.ones((1, len(th))), b_eq=[1.0], bounds=(0, None), method="highs")
    primal = -res.fun
    lam = -res.ineqlin.marginals  # >= 0
    lam0 = -res.eqlin.marginals[0]
    lam = np.maximum(lam, 0.0)
    # certify: f(theta) = lam0 + sum lam_j h_j(theta) - theta >= 0 on [0,1]
    N = 2_000_001
    fine = np.linspace(0, 1, N)
    f = lam0 - fine
    for j, l in zip(js, lam):
        if l > 0:
            f = f + l * h(j, fine)
    lip = 1.0 + sum((j + 1) * l for j, l in zip(js, lam))
    margin = max(0.0, -f.min() + lip * (1.0 / (N - 1)) / 2)
    dual = lam0 + float(np.dot(lam, b)) + margin
    supp = [(j, round(float(l), 4), round(bb, 5)) for j, l, bb in zip(js, lam, b) if l > 1e-7]
    Jmax = max(s[0] for s in supp)
    return primal, dual, margin, supp, Jmax, dict(zip(js, b))

if __name__ == "__main__":
    claims = {3: (0.4963, 0.4974, 0.4984), 4: (0.3075, 0.3083, 0.3090), 7: (0.0618, 0.0620, 0.0622), 10: (0.01109, 0.01115, 0.01119)}
    generic = {3: 0.3276, 4: 0.2051, 7: 0.04165, 10: 0.00724}
    rates = [int(a) for a in sys.argv[1:]] or [3, 4, 7, 10]
    for r in rates:
        p0, d0, m0, s0, J0, _ = run(r, 22, slack=False)
        print("rate 2^-%d no slack (generic): primal %.5f dual %.5f (claimed %.5f) support j = %s" % (r, p0, d0, generic[r], [s[0] for s in s0]), flush=True)
        for idx, lgn in enumerate((20, 22, 24)):
            p, d, m, s, Jm, bs = run(r, lgn)
            print("rate 2^-%d n=2^%d J=0 slack: primal %.5f <= tau* <= dual %.5f (margin %.1e) claimed %.5f ; J0 = %d, list <= %.1f/eta" % (
                r, lgn, p, d, m, claims[r][idx], Jm, Jm * (1 - d)), flush=True)
            print("    support (j, lambda_j, right side):", s, flush=True)
