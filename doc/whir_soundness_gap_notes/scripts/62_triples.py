#!/usr/bin/env python3
"""Note 62, section 7: constants of Theorem H_3 (conditional on Hypothesis L) and the lists.

E_T  : least E with q^(E+2) >= 2^132 |Pi(2k+E)| q^(2 a0) (1 + q^-(1-2 gamma))^n
       (Proposition T against the number of patterns; |Pi| bounded by (n+1)^3 times
       its largest multinomial term, found on the symmetric line s1 = s2 = s3).
E_3  : max(2 e_2 - 2, E_T) + extra   (extra: allowance for Hypothesis L, in units of n)
alpha*: root of alpha^2 (3 - alpha) = (2k + E_3)/n; queries = ceil(108 / log2(1/alpha)).
M_0  : three-wise Johnson bound (note 44 Lemma 5.2) at alpha* + margin.
Run: python3 62_triples.py   (or through 62_constants.py triples)
"""
import math, os, importlib.util

_d = os.path.dirname(os.path.abspath(__file__))
_s = importlib.util.spec_from_file_location("c62", os.path.join(_d, "62_constants.py"))
c62 = importlib.util.module_from_spec(_s)
_s.loader.exec_module(c62)
LG, LN2, LOGQ = math.lgamma, math.log(2.0), 64


def log2_multinomial(n, parts):
    rest = n - sum(parts)
    if rest < 0 or min(parts) < 0:
        return -math.inf
    return (LG(n + 1) - sum(LG(p + 1) for p in parts) - LG(rest + 1)) / LN2


def log2_patterns(n, weight, A2):
    """upper bound for log2 |Pi|: patterns of the given weight with |U3| + s_i <= A2."""
    def f(u3):
        s = (weight - 2 * u3) / 3.0
        if s < 0 or u3 + s > A2 or u3 + 3 * s > n:
            return -math.inf
        return log2_multinomial(n, [u3, s, s, s])
    lo = max(0.0, weight - n)          # u3 + 3s <= n  <=>  u3 >= weight - n
    hi = min(weight / 2.0, 3 * A2 - weight)
    if hi < lo:
        return -math.inf
    for _ in range(200):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if f(m1) < f(m2):
            lo = m1
        else:
            hi = m2
    return f((lo + hi) / 2) + 3 * math.log2(n + 1)


def E_T(n, k, A2, gamma, a0):
    E = 0
    slack = n * math.log2(1.0 + 2.0 ** (-LOGQ * (1 - 2 * gamma))) + 2 * a0 * LOGQ
    while True:
        need = 132 + log2_patterns(n, 2 * k + E + 1, A2) + slack
        if LOGQ * (E + 2) >= need:
            return E
        E += max(1, int((need - LOGQ * (E + 2)) / (2 * LOGQ)))


def alpha_star(two_rho_eff):
    lo, hi = 0.0, 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if mid * mid * (3 - mid) > two_rho_eff:
            hi = mid
        else:
            lo = mid
    return hi


def M0(alpha, two_rho_eff):
    A = alpha * alpha * (3 - alpha) - two_rho_eff
    Bc = 3 * (alpha + alpha * alpha - two_rho_eff)
    return max(1 / (1 - alpha), Bc / A)


def queries(alpha):
    return math.ceil(108 / math.log2(1 / alpha))


GAMMA = {  # gamma at density phi (N = 25, failure 2^-129), from 62_expansion_output.txt
    6: {1 / 16: 0.286, 1 / 8: 0.292, 1 / 4: 0.351, 1 / 2: 0.501},
    8: {1 / 16: 0.192, 1 / 8: 0.214, 1 / 4: 0.256, 1 / 2: 0.371},
    10: {1 / 16: 0.151, 1 / 8: 0.168, 1 / 4: 0.200, 1 / 2: 0.288},
}


def main():
    print("Theorem H_3 constants (conditional on Hypothesis L). q = 2^64, gamma = 0.40, a0 = 0 unless noted.")
    print("rate   N   e2/n     E_T/n    E_3/n    alpha*  queries  Johnson(queries)  M0(+.005) M0(+.01) | E_3+0.02n: alpha*, queries")
    for N in [10, 16, 20, 25, 28]:
        n = 2 ** N
        for r in [2, 4, 8, 16]:
            k = n // r
            a0 = 16 if N < 20 else 0
            e2 = c62.e2_expanding(n, k, a0)
            A2 = k + e2 - 1
            ET = E_T(n, k, A2, 0.40, a0)
            E3 = max(2 * e2 - 2, ET)
            t = (2 * k + E3) / n
            al = alpha_star(t)
            al2 = alpha_star(t + 0.02)
            joh = math.sqrt(1 / r)
            print("1/%-3d %3d  %.5f  %.5f  %.5f  %.4f  %4d     %.4f (%3d)     %7.1f  %7.1f   | %.4f, %d"
                  % (r, N, e2 / n, ET / n, E3 / n, al, queries(al), joh, queries(joh),
                     M0(al + 0.005, t), M0(al + 0.01, t), al2, queries(al2)))
    print()
    print("which d makes Proposition T cover all transversal configurations (needs gamma(2 rho) < 1/2), N = 25:")
    for d in (6, 8, 10):
        row = []
        for r in (4, 8, 16):
            g1, g2 = GAMMA[d][1 / r], GAMMA[d][2 / r]
            row.append("rate 1/%d: gamma(rho) = %.3f, gamma(2 rho) = %.3f %s" % (r, g1, g2, "ok" if g2 < 0.5 else "NO"))
        print("  d = %2d: gamma(1/2) = %.3f (rate 1/2: free part only);  " % (d, GAMMA[d][0.5]) + ";  ".join(row))


if __name__ == "__main__":
    main()
