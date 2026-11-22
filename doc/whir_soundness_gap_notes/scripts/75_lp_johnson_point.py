# Referee 75: the list bound from the finite program at the Johnson radius itself: smallest M with tau_M(rho) < sqrt(rho) (exact certificates).
import importlib.util, math
from fractions import Fraction
spec = importlib.util.spec_from_file_location("lp75", "75_lp.py"); lp = importlib.util.module_from_spec(spec); spec.loader.exec_module(lp)
for lg in (3, 4, 5, 7, 10):
    rho = Fraction(1, 2 ** lg); J = math.sqrt(float(rho)); out = []
    for M in range(3, 80):
        val, bound = lp.finite_lp(rho, M, exact=True)
        out.append((M, float(bound)))
        if float(bound) < J: break
    M, b = out[-1]; pm, pb = out[-2]
    print(f"rate 2^-{lg}: Johnson radius {J:.6f}; tau_{pm} <= {pb:.6f}, tau_{M} <= {b:.6f} < sqrt(rho): at agreement sqrt(rho) n or more, at most {M - 1} codewords")
