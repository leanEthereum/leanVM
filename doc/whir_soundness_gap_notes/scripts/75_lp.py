# Referee 75, item 2: the linear programs behind note 68 Section 11, with certificates.
#  (1) limit program tau*_J(rho) = sup E[theta] s.t. E[h_j(theta)] <= j rho, j <= J: grid primal (a lower bound on the sup)
#      and a dual certificate checked on a fine grid with a Lipschitz margin (an upper bound on the sup);
#  (2) finite program tau_M(rho): hypergeometric constraints (F) for a list of M members, dual certificate checked in exact
#      rational arithmetic for M <= EXACT_MAX;
#  (3) Proposition R2: tau <= tau*_J + (1 - tau*_J) J / M, compared with (2), and the table of smallest agreements.
import sys, math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.stats import hypergeom

def h(j, th):
    return 1 - (1 - th) ** (j + 1) - (j + 1) * th * (1 - th) ** j

def grid_for(rho):
    g = np.concatenate([np.linspace(0, 1, 4001), np.geomspace(rho / 64, 1, 3000)])
    return np.unique(g)

def limit_lp(rho, J):
    """returns (lower, upper, lam0, lam[1..J]) for tau*_J(rho)"""
    J = min(J, math.ceil(1 / rho) - 1)   # constraints with j rho >= 1 are vacuous
    g = grid_for(rho)
    js = np.arange(1, J + 1)
    A = np.array([h(j, g) for j in js])
    res = linprog(-g, A_ub=A, b_ub=js * rho, A_eq=np.ones((1, len(g))), b_eq=[1.0], bounds=(0, None), method="highs")
    lower = -res.fun
    lam = np.maximum(-res.ineqlin.marginals, 0.0); lam0 = float(-res.eqlin.marginals[0])
    # certificate: p(theta) = lam0 + sum lam_j h_j(theta) - theta >= 0 on [0,1]; fine grid plus Lipschitz constant 1 + sum lam_j (j+1)
    fine = np.unique(np.concatenate([np.linspace(0, 1, 4000001), np.geomspace(rho / 4096, 1, 200001)]))
    p = lam0 - fine
    for j, l in zip(js, lam):
        if l > 0: p = p + l * h(int(j), fine)
    lip = 1 + float(np.sum(lam * (js + 1)))
    gap = float(np.max(np.diff(fine)))
    deficit = max(0.0, -(float(p.min()) - lip * gap / 2))
    upper = lam0 + deficit + rho * float(np.sum(lam * js))
    return lower, upper, lam0 + deficit, lam

def Hmat(M, J):
    c = np.arange(0, M + 1)
    return np.array([hypergeom.sf(1, M, c, j + 1) for j in range(1, J + 1)])

def H_exact(j, c, M):
    tot = math.comb(M, j + 1)
    return 1 - Fraction(math.comb(M - c, j + 1) + c * math.comb(M - c, j), tot)

def finite_lp(rho_frac, M, exact=True):
    """tau_M: max sum (c/M) x_c s.t. sum x_c = 1, sum H_j(c;M) x_c <= j rho (the -1/n is dropped). Returns (float value, certified upper bound)"""
    rho = float(rho_frac)
    J = min(M - 1, math.ceil(1 / rho) - 1)
    c = np.arange(0, M + 1); js = np.arange(1, J + 1)
    A = Hmat(M, J)
    res = linprog(-c / M, A_ub=A, b_ub=js * rho, A_eq=np.ones((1, M + 1)), b_eq=[1.0], bounds=(0, None), method="highs")
    val = -res.fun
    lam = np.maximum(-res.ineqlin.marginals, 0.0); lam0 = float(-res.eqlin.marginals[0])
    if not exact:
        slack = lam0 + lam @ A - c / M
        return val, lam0 + max(0.0, -float(slack.min())) + rho * float(np.sum(lam * js))
    lamq = {int(j): Fraction(float(l)).limit_denominator(10 ** 12) for j, l in zip(js, lam) if l > 1e-13}
    lam0q = Fraction(lam0).limit_denominator(10 ** 12)
    worst = Fraction(0)
    for cc in range(M + 1):
        s = lam0q + sum(l * H_exact(j, cc, M) for j, l in lamq.items()) - Fraction(cc, M)
        if s < worst: worst = s
    bound = lam0q - worst + rho_frac * sum(j * l for j, l in lamq.items())
    return val, bound

def finite_cert_big(rho, M):
    """certified upper bound on tau_M for large M: dual from the program on a subsample of c, then checked on every c = 0..M (floats, gammaln)"""
    from scipy.special import gammaln
    J = math.ceil(1 / rho) - 1; js = np.arange(1, J + 1)
    cs = np.unique(np.concatenate([np.arange(0, 3001), np.geomspace(3001, max(M, 3002), 3000).astype(np.int64), [M]])); cs = cs[cs <= M]
    A = np.array([hypergeom.sf(1, M, cs, j + 1) for j in js])
    res = linprog(-cs / M, A_ub=A, b_ub=js * rho, A_eq=np.ones((1, len(cs))), b_eq=[1.0], bounds=(0, None), method="highs")
    lam = np.maximum(-res.ineqlin.marginals, 0.0); lam0 = float(-res.eqlin.marginals[0])
    c = np.arange(0, M + 1, dtype=np.float64); slack = lam0 - c / M
    def logcomb(a, b):  # log C(a, b), -inf where a < b
        with np.errstate(invalid="ignore", divide="ignore"):
            return np.where(a >= b, gammaln(a + 1) - gammaln(b + 1) - gammaln(np.maximum(a - b, 0) + 1), -np.inf)
    for j, l in zip(js, lam):
        if l <= 1e-13: continue
        j = int(j); lt = logcomb(np.float64(M), j + 1)
        p0 = np.exp(logcomb(M - c, j + 1) - lt); p1 = c * np.exp(logcomb(M - c, j) - lt)
        slack = slack + l * (1 - p0 - p1)
    return lam0 + max(0.0, -float(slack.min())) + 1e-8 + rho * float(np.sum(lam * js))

def johnson_min_agreement(rho, Lam):
    # smallest tau with (tau - rho)/(tau^2 - rho) <= Lam: Lam tau^2 - tau - (Lam - 1) rho = 0
    return (1 + math.sqrt(1 + 4 * Lam * (Lam - 1) * rho)) / (2 * Lam)

if __name__ == "__main__":
    EXACT_MAX = 1025
    print("== (1) limit thresholds tau* (all j with j rho < 1): grid primal <= tau* <= certified dual ==")
    star = {}
    for lg in (1, 2, 3, 4, 5, 7, 10):
        rho = 2.0 ** -lg
        lo, up, lam0, lam = limit_lp(rho, 10 ** 9)
        star[lg] = (lo, up)
        nz = [(j + 1, round(float(l), 5)) for j, l in enumerate(lam) if l > 1e-9]
        print(f"rate 2^-{lg}: {lo:.7f} <= tau* <= {up:.7f}   Johnson {math.sqrt(rho):.6f}   capacity {rho:.6f}   dual support (j, lambda_j): {nz[:8]}{' ...' if len(nz) > 8 else ''} ({len(nz)} constraints active)")
    sys.stdout.flush()
    print("\n== (2) finite program tau_M(rho), certified upper bound (exact rationals for M <= %d), and Proposition R2 with the best J ==" % EXACT_MAX)
    cache = {}
    def tstar(lg, J):
        if (lg, J) not in cache: cache[(lg, J)] = limit_lp(2.0 ** -lg, J)[1]
        return cache[(lg, J)]
    def r2(lg, M):
        J0 = 2 ** lg - 1; best = (2.0, 0)
        cand = sorted(set([j for j in (1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 15, 20, 24, 31, 40, 48, 63, 80, 96, 127, 160, 200, 255, 320, 400, 511, 640, 800, 1023) if j <= J0 and j < M]))
        for J in cand:
            t = tstar(lg, J); b = t + (1 - t) * J / M
            if b < best[0]: best = (b, J)
        return best
    for lg in (3, 4, 7, 10):
        rho_frac = Fraction(1, 2 ** lg)
        print(f"rate 2^-{lg}:")
        prev = 2.0
        for M in (3, 4, 5, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 400, 1025):
            val, bound = finite_lp(rho_frac, M, exact=(M <= EXACT_MAX))
            b2, Jb = r2(lg, M)
            jb = johnson_min_agreement(float(rho_frac), M - 1)
            print(f"  M = {M:5d}: tau_M = {val:.6f} (M (tau_M - tau*) = {M * (val - star[lg][0]):.3f}), certified <= {float(bound):.6f} ({'exact' if M <= EXACT_MAX else 'float'}); R2 bound {b2:.6f} (J = {Jb}); Johnson's bound for M members {jb:.6f}{'   NOT MONOTONE' if val > prev + 1e-9 else ''}")
            prev = val; sys.stdout.flush()
    print("\n== (3) smallest agreement above which every list has at most Lambda members (conditional on Q_t of the generic tree code) ==")
    print("Lambda = 2^10: finite program at M = 1025 (exact certificate); 2^20: finite program at M = 2^20 + 1 (float certificate on every c); 2^40: Proposition R2 at M = 2^40 + 1")
    for lg in (3, 4, 7, 10):
        rho = 2.0 ** -lg
        _, b10 = finite_lp(Fraction(1, 2 ** lg), 1025, exact=True); b10 = float(b10)
        b20 = min(b10, finite_cert_big(rho, 2 ** 20 + 1), r2(lg, 2 ** 20 + 1)[0]); r20 = r2(lg, 2 ** 20 + 1)[0]
        b40 = min(b20, r2(lg, 2 ** 40 + 1)[0])
        chk = finite_cert_big(rho, 1025)
        print(f"rate 2^-{lg}: tau* in [{star[lg][0]:.7f}, {star[lg][1]:.7f}]; list <= 2^10 above {b10:.7f} (large-M routine at M = 1025, as a check: {chk:.7f}); <= 2^20 above {b20:.7f} (R2 alone: {r20:.7f}); <= 2^40 above {b40:.7f}; "
              f"Johnson: {johnson_min_agreement(rho, 2 ** 10):.6f}, {johnson_min_agreement(rho, 2 ** 20):.6f}, {johnson_min_agreement(rho, 2 ** 40):.6f}; capacity {rho:.6f}; "
              f"closed form (1 - tau*)/(rho eta) = 2^10, 2^20, 2^40 at tau* + {(1 - star[lg][1]) / rho / 2 ** 10:.6f}, {(1 - star[lg][1]) / rho / 2 ** 20:.2e}, {(1 - star[lg][1]) / rho / 2 ** 40:.2e}")
        sys.stdout.flush()
