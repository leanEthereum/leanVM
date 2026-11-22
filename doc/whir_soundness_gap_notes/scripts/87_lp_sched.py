#!/usr/bin/python3
# Referee 87: the "cheap checks" column of note 84, Theorem 8.2, recomputed (arithmetic only: it assumes the top
# conditions of note 84 Section 6 for the schedule t -> J_t). Same program as 87_lp.py with J depending on t.
import importlib.util, os, sys
import numpy as np
from scipy.optimize import linprog
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
E = load("87_eps"); LP = load("87_lp")
def run(r, lgn, sched):
    rho = 2.0 ** -r; v = lgn - r; js, b = [], []
    for j in LP.constraint_set(r):
        J = sched.get(j + 1, 0)
        e0, lam0, _, _ = E.best(r, v, J, 140, j + 1, step=1.0, lo=0.05, hi=40.0)
        e, lam, _, _ = E.best(r, v, J, 140, j + 1, step=0.05, lo=max(0.05, lam0 - 1.0), hi=lam0 + 1.0)
        rhs = j * rho + min(e, e0)
        if rhs < 1.0:
            js.append(j); b.append(rhs)
    th = np.unique(np.concatenate([np.linspace(0, 1, 4001), np.geomspace(1e-6, 1, 6000)]))
    A = np.array([LP.h(j, th) for j in js])
    res = linprog(-th, A_ub=A, b_ub=np.array(b), A_eq=np.ones((1, len(th))), b_eq=[1.0], bounds=(0, None), method="highs")
    lam = np.maximum(-res.ineqlin.marginals, 0.0); lam0 = -res.eqlin.marginals[0]
    N = 2_000_001; fine = np.linspace(0, 1, N); f = lam0 - fine
    for j, l in zip(js, lam):
        if l > 0: f = f + l * LP.h(j, fine)
    lip = 1.0 + sum((j + 1) * l for j, l in zip(js, lam))
    dual = lam0 + float(np.dot(lam, b)) + max(0.0, -f.min() + lip / (N - 1) / 2)
    return -res.fun, dual
for r, sched, claim in ((3, {2: 3, 3: 2, 4: 1, 5: 1}, "0.3883, 0.3891, 0.3898"), (4, {2: 2, 3: 1, 4: 1}, "0.2640, 0.2646, 0.2651"), (7, {2: 2, 3: 1, 4: 1}, "0.0559, 0.0561, 0.0562"), (10, {2: 1, 3: 1, 4: 1}, "0.01048, 0.01054, 0.01058")):
    out = [run(r, lgn, sched) for lgn in (20, 22, 24)]
    print("rate 2^-%d cheap schedule %s: primal/dual %s ; note 84: %s" % (r, sched, ", ".join("%.5f/%.5f" % o for o in out), claim), flush=True)
