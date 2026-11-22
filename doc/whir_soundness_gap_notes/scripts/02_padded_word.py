"""Full list (exhaustive oracle) of the padded-hyperplane word of note 01 / [DKTZ26] at rate 1/2, as a comparison
point for the simple common-top maxima: w = X^(n/2) Z_C(X), C = a codimension-2 flat minus one point.
P_H = w - Z_H Z_C has degree <= n/2 - 1 and agrees with w on H + C for every affine hyperplane H.

usage: python3 02_padded_word.py <lists-binary> N
"""
import sys, os, subprocess, importlib.util
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
F = gf.GF(64)
binary, N = sys.argv[1], int(sys.argv[2])
n = 1 << N
D = list(range(n))
C = [x for x in D if x >> (N - 2) == 1][1:]  # the flat {top two coordinates = (1, 0)} minus one point
ZC = F.locator(C)
vals = [F.mul(F.pow(x, n // 2), F.poly_eval(ZC, x)) for x in D]
T = n // 2 + n // 8 - 1
inp = " ".join(f"{x:x}" for x in D) + "\n" + " ".join(f"{v:x}" for v in vals) + "\n"
out = subprocess.run([binary, "profile", "64", "1b", str(n), str(n // 2), str(T)], input=inp, capture_output=True, text=True).stdout
print(f"N={N} n={n}: |C| = {len(C)}; polynomials of degree < n/2 by exact agreement (>= {T}): {out.strip()}")
