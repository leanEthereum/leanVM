#!/usr/bin/env python3
"""Sections of the flat cubic inside the window (a_1, 1/2) at rate 1/4 on the dense domain D = F_{2^11}
(Section 4.3 of 43-low-rate-residuals.md).

n = 2048, word y = x^1023.  Lam_16 has F_2-dimension 22 (lambda = g0 + g8 t^8 + g16 t^16 with the two necklace
relations).  The script draws random elements with g16 != 0, builds the two sections, keeps those that are
polynomials of degree < n/4 = 512 and checks: agreement exactly 991 = 0.4839 n > a_1 n = 960.1, d/dX E(X, P) = 0,
M_P = X P^2 + 1 divides X^(n-1) + 1.  It prints the fraction found against the prediction
2047*496 / (2*(2^22 - 2^11)) = 0.1211 from the count 2^(2t)(2^N - 1)(992/2048) of minimum-weight words (t = 5).
Run: python3 43_gold_window.py [samples]   (default 60, about 1.5 min)
"""
import random
import sys
import importlib

sys.path.insert(0, sys.path[0] or ".")
gfm = importlib.import_module("43_gf")
fs = importlib.import_module("43_flat_sections")

N = 11
n = 1 << N
F = gfm.GF(N)
basis = [1 << i for i in range(N)]
D = F.span(basis)
LD = F.subspace_poly(basis)
assert LD == [0, 1] + [0] * (n - 2) + [1]
y = {a: F.pow(a, n // 2 - 1) for a in D if a}
ker = fs.lam_space(F, LD, N, 16)
assert len(ker) == 22
samples = int(sys.argv[1]) if len(sys.argv) > 1 else 60
rnd = random.Random(11)
found = tried = 0
first = None
while tried < samples:
    g = [0] * 17
    for t in range(22):
        if rnd.random() < 0.5:
            g = [a ^ b for a, b in zip(g, ker[t])]
    if g[16] == 0:
        continue
    tried += 1
    for (P, ag) in fs.sections_of(F, LD, N, D, y, g):
        assert ag == 991 and F.deg(P) == (991 - 1) // 2 and F.deg(P) < n // 4
        # section: E(X,P) = X P^3 + P + X^(n/2-1) in F[X^2]
        EP = F.padd(F.padd([0] + F.ppow(P, 3), P), [0] * (n // 2 - 1) + [1])
        assert F.is_even(EP)
        M = F.padd([0] + F.psq(P), [1])
        assert not F.pdivmod([1] + [0] * (n - 2) + [1], M)[1]
        found += 1
        if first is None:
            first = P
print(f"D = F_2^11, n = {n}: {found} polynomial sections of degree 495 < n/4 with agreement 991 = {991 / n:.4f} n "
      f"from {tried} random lambda with deg 16; observed rate per section {found / (2 * tried):.3f} "
      f"(predicted 0.121); a_1 n = {0.468792 * n:.1f}")
print("so the list of x^1023 at agreement 991 has about 2047*496 = 1015312 members against 2047 flats at 1023")
