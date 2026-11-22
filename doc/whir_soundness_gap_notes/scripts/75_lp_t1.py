# Referee 75: what the limit program gives if Q_t (t >= 4) held only with the T1 values measured here, (t-1)k + k/2 - 1 coincidence
# leaves (lifts of the Desargues configuration), Q_2 and Q_3 as in T2. HYPOTHETICAL: the true T1 maxima are not known.
import math, numpy as np
from scipy.optimize import linprog
def h(j, th): return 1 - (1 - th) ** (j + 1) - (j + 1) * th * (1 - th) ** j
for lg in (3, 4, 5, 7):
    rho = 2.0 ** -lg; g = np.unique(np.concatenate([np.linspace(0, 1, 4001), np.geomspace(rho / 64, 1, 3000)]))
    out = []
    for extra in (0.0, 0.5, 1.0):
        js = [j for j in range(1, 4 * 2 ** lg) if (j + (extra if j >= 3 else 0)) * rho < 1]
        A = np.array([h(j, g) for j in js]); b = np.array([(j + (extra if j >= 3 else 0)) * rho for j in js])
        res = linprog(-g, A_ub=A, b_ub=b, A_eq=np.ones((1, len(g))), b_eq=[1.0], bounds=(0, None), method="highs")
        out.append(-res.fun)
    print(f"rate 2^-{lg}: threshold with Q_t exact {out[0]:.4f}; with (t-1)k + k/2 for t >= 4: {out[1]:.4f}; with (t-1)k + k for t >= 4: {out[2]:.4f}; Johnson {math.sqrt(rho):.4f}")
