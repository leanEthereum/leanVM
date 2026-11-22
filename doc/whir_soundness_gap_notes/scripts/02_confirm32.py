"""Independent confirmation at n = 32, rate 1/2, with the exhaustive list oracle (all polynomials, not only
common-top ones), on leanVM's domain shape D = span(1, x, ..., x^4) in GF(2^64).

  a) w = L_U^5, degree <= 16 (k = 17), agreement >= 20: Theorem 5 predicts at least 1400.
  b) w = (L_U^5 - c)/(X - p), degree < 16, agreement >= 19: at least 875.
  c) w = shared top of the largest generic common-top class at T = 19 (complements of the 1323 dumped 13-sets),
     degree < 16, agreement >= 19: at least 1323.

usage: python3 02_confirm32.py <lists-binary> <ct32 dump file of a generic run> a|b|c
"""
import sys, os, subprocess, random, importlib.util
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
F = gf.GF(64)
binary, dumpfile, which = sys.argv[1], sys.argv[2], sys.argv[3]
N, n = 5, 32
D = gf.span(gf.power_basis(F, N))
Ub = [D[5], D[18]]
LU = gf.subspace_poly(F, Ub)
LUf = [0] * 5
for i, c in enumerate(LU):
    LUf[1 << i] = c
w = [1]
for _ in range(5):
    w = F.poly_mul(w, LUf)
if which == "a":
    k, T, vals = 17, 20, [F.poly_eval(w, x) for x in D]
elif which == "b":
    p = D[1]
    c = F.poly_eval(w, p)
    w[0] ^= c
    q = [0] * (len(w) - 1)
    carry = 0
    for d in range(len(w) - 1, 0, -1):
        carry = w[d] ^ F.mul(carry, p)
        q[d - 1] = carry
    k, T, vals = 16, 19, [F.poly_eval(q, x) for x in D]
else:
    line = next(l for l in open(dumpfile) if l.startswith("dump T=13 t=3:"))
    masks = [int(x, 16) for x in line.split(":")[1].split()]
    tops = set()
    for mk in masks:
        S = [D[i] for i in range(n) if not mk >> i & 1]
        Z = F.locator(S)
        tops.add(tuple(Z[16:]))
    assert len(tops) == 1, "complements do not share the top on this domain"
    top = [0] * 16 + list(tops.pop())
    k, T, vals = 16, 19, [F.poly_eval(top, x) for x in D]
    print(f"c) {len(masks)} dumped 13-sets: complements share all coefficients of degree >= 16 on the power-basis domain")
inp = " ".join(f"{x:x}" for x in D) + "\n" + " ".join(f"{v:x}" for v in vals) + "\n"
out = subprocess.run([binary, "profile", "64", "1b", str(n), str(k), str(T)], input=inp, capture_output=True, text=True).stdout
print(f"{which}) degree < {k}, exact agreement -> number of polynomials: {out.strip()}")
