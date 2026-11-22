#!/usr/bin/env python3
"""Note 84, Section 8: referee 75's limit program with the slack of Theorem 5.1.

  tau*_eps = sup E[theta]  s.t.  E[h_j(theta)] <= j rho + eps_{j+1},  j in a set JS,
  h_j(theta) = Pr[Bin(j+1, theta) >= 2].

Upper bound by a dual certificate lam0 + sum lam_j h_j(theta) >= theta on [0,1], checked on a
fine grid with a Lipschitz margin (constant 1 + sum lam_j (j+1)), exactly as scripts/75_lp.py.
Using a subset JS of the constraints can only raise the bound, so every value printed is a valid
upper bound. Needs numpy and scipy (/usr/bin/python3).
"""
import importlib.util
import math
import os
import sys

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("eps84", os.path.join(HERE, "84_eps.py"))
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)

P_LOG2 = -140.0  # per-t failure probability 2^-140: at most 2^10 values of t, total 2^-130


def h(j, th):
    return 1 - (1 - th) ** (j + 1) - (j + 1) * th * (1 - th) ** j


def certified(rho, js, b):
    """js: constraint indices, b: right sides. Returns (grid primal, certified dual, support)."""
    js = np.array(js)
    b = np.array(b)
    g = np.unique(np.concatenate([np.linspace(0, 1, 4001), np.geomspace(rho / 64, 1, 3000)]))
    A = np.array([h(int(j), g) for j in js])
    res = linprog(-g, A_ub=A, b_ub=b, A_eq=np.ones((1, len(g))), b_eq=[1.0], bounds=(0, None), method="highs")
    lower = -res.fun
    lam = np.maximum(-res.ineqlin.marginals, 0.0)
    lam[lam < 1e-12] = 0.0
    lam0 = float(-res.eqlin.marginals[0])
    fine = np.unique(np.concatenate([np.linspace(0, 1, 2000001), np.geomspace(rho / 4096, 1, 200001)]))
    pfun = lam0 - fine
    for j, l in zip(js, lam):
        if l > 0:
            pfun = pfun + l * h(int(j), fine)
    lip = 1 + float(np.sum(lam * (js + 1)))
    gap = float(np.max(np.diff(fine)))
    deficit = max(0.0, -(float(pfun.min()) - lip * gap / 2))
    upper = lam0 + deficit + float(np.sum(lam * b))
    supp = [(int(j), float(l)) for j, l in zip(js, lam) if l > 0]
    return lower, upper, supp


def j_set(r):
    top = 2 ** r - 1
    js = set(range(1, min(top, 48) + 1))
    x = 48.0
    while x < top:
        x *= 1.12
        js.add(min(top, int(round(x))))
    return sorted(js)


def slack(r, logn, t, J):
    L, nd = E.graphic(t)
    val, _ = E.best(r, logn - r, J, L, nd, p_log2=P_LOG2, lo=0.5, hi=40.0, step=0.1)
    return val


def main_part(r, logn, t):
    """Main part only at J = 0 and the lambda that minimizes the full slack (reported, not a theorem)."""
    L, nd = E.graphic(t)
    _, lam = E.best(r, logn - r, 0, L, nd, p_log2=P_LOG2, lo=0.5, hi=40.0, step=0.1)
    return E.eps(r, logn - r, 0, L, nd, P_LOG2, 0.0, lam, parts=True)[1]


# checked-top schedules: t -> J for which Top_{Delta_t}(0) on T_J is an enumeration (Section 6.3)
# "checked": at most 2^35 minors; "heavy": at most 2^44 minors
CHECKED = {
    3: {2: 3, 3: 2, 4: 1, 5: 1},
    4: {2: 2, 3: 1, 4: 1},
    7: {2: 2, 3: 1, 4: 1},
    10: {2: 1, 3: 1, 4: 1},
}
HEAVY = {
    3: {2: 3, 3: 2, 4: 1, 5: 1, 6: 1},
    4: {2: 3, 3: 2, 4: 1, 5: 1},
    7: {2: 2, 3: 1, 4: 1},
    10: {2: 2, 3: 1, 4: 1},
}
NAMES = ("generic", "J0", "checked", "heavy", "main-only")


def run(r, logn):
    rho = 2.0 ** -r
    js_all = j_set(r)
    out = {}
    for name in NAMES:
        js, b = [], []
        for j in js_all:
            t = j + 1
            if name == "generic":
                e = 0.0
            elif name == "J0":
                e = slack(r, logn, t, 0)
            elif name == "checked":
                e = slack(r, logn, t, CHECKED[r].get(t, 0))
            elif name == "heavy":
                e = slack(r, logn, t, HEAVY[r].get(t, 0))
            else:
                e = main_part(r, logn, t)
            if j * rho + e < 1.0:
                js.append(j)
                b.append(j * rho + e)
        lo, up, supp = certified(rho, js, b)
        out[name] = (lo, up, supp, dict(zip(js, b)))
    return out


if __name__ == "__main__":
    for r in (3, 4, 7, 10):
        rho = 2.0 ** -r
        for logn in (20, 22, 24):
            res = run(r, logn)
            print(f"rate 2^-{r}, n = 2^{logn}: Johnson sqrt(rho) = {math.sqrt(rho):.5f}, capacity {rho:.6f}")
            for name in NAMES:
                lo, up, supp, bmap = res[name]
                jmax = max(j for j, _ in supp)
                e1 = bmap.get(1, float('nan')) - rho
                print(f"  {name:10s}: {lo:.5f} <= tau* <= {up:.5f}   eps_2 = {e1:.5f}, Johnson of the code sqrt(rho+eps_2) = {math.sqrt(rho + e1):.5f}"
                      f"   list at tau*+eta <= {jmax}*(1-tau*)/eta = {jmax*(1-up):.1f}/eta")
                print("              support (j, lambda_j, right side): " + ", ".join(f"({j}, {l:.4f}, {bmap[j]:.5f})" for j, l in supp))
            sys.stdout.flush()
