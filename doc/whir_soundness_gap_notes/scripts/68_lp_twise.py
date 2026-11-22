# Limit LP (list size -> infinity): maximize E[theta] over probability measures mu on [0,1]
# subject to E[h_j(theta)] <= j*rho for j = 1..J, where h_j(theta) = P[Bin(j+1, theta) >= 2].
# This is the agreement threshold above which the t-wise coincidence bounds (each leaf counted once,
# at most (t-1)k - 1 leaves where two of t codewords agree) forbid unbounded lists.
import sys, math
try:
    from scipy.optimize import linprog
    import numpy as np
except Exception as e:
    print("no scipy:", e); sys.exit(0)

def h(j, th):
    t = j + 1
    return 1 - (1 - th) ** t - t * th * (1 - th) ** (t - 1)

def solve(rho, G=2001):
    J = int(math.ceil(1 / rho)) + 2
    grid = np.linspace(0, 1, G)
    c = -grid
    A = np.array([[h(j, th) for th in grid] for j in range(1, J + 1)])
    b = np.array([j * rho for j in range(1, J + 1)])
    res = linprog(c, A_ub=A, b_ub=b, A_eq=np.ones((1, G)), b_eq=[1.0], bounds=(0, None), method="highs")
    mu = res.x
    supp = [(round(float(grid[i]), 4), round(float(mu[i]), 4)) for i in range(G) if mu[i] > 1e-6]
    return -res.fun, supp

for lg in (1, 2, 3, 4, 5, 7, 10):
    rho = 2.0 ** -lg
    val, supp = solve(rho)
    J = math.sqrt(rho)
    q = lambda t: 108 / math.log2(1 / t)
    print(f"rate 2^-{lg}: LP threshold {val:.4f}  Johnson {J:.4f}  capacity {rho:.4f}  queries {q(val):.1f} vs {q(J):.1f}  support {supp[:6]}")
