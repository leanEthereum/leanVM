#!/usr/bin/env python3
"""53_tight.py: synthetic pencils at infinity (Section 3.6 of 53-goppa-structure-degenerate.md).

Centre psi = X^p (a polynomial, so the divisor is at infinity), rate 1/2, Delta = n/2. A clean section with
theta = h polynomial is a P of degree <= Delta with X^p + P = Lambda_O h^2, O a subset of D, |O| > Delta; then
P = X^p mod Lambda_O, and the condition is: X^p div Lambda_O is a square and deg(X^p mod Lambda_O) <= Delta.
Necessary (the code): |O| = p mod 2 and p_k(O) = 0 for 1 <= k <= p - Delta - 1.

For each (domain, p) the script enumerates the whole coset of the code, and reports
   the number of its words of weight >= A, and how many of them are sections (list members of the word x^p),
which measures what the F_2-linear relaxation loses (the even elementary symmetric functions).

Run: python3 53_tight.py     (about 1 minute)
"""
import importlib
import sys

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("53_lib")


def run(m, N, kind, p, Amin, seed=3):
    F = L.GF(m)
    n = 1 << N
    basis = L.domain(F, N, kind, seed)
    D = F.span(basis)
    Delta = n // 2
    g = p - Delta - 1
    rows = L.rows_inf(F, D, g, parity=False)
    code = L.f2_kernel(rows)
    dim = len(code)
    if dim > 24:
        print(f"  {kind:5s} GF(2^{m}) n={n} p={p}: dim {dim}, skipped")
        return
    Xp = [0] * p + [1]
    tot, sec, by = 0, 0, {}
    cur = 0
    for i in range(1 << dim):
        if i:
            cur ^= code[(i & -i).bit_length() - 1]
        w = bin(cur).count("1")
        if w < Amin or (w - p) & 1 or w > p:
            continue
        tot += 1
        O = L.mask_pts(D, cur)
        q, r = F.pdivmod(Xp, L.locator(F, O))
        if L.is_square(F, q) and L.deg(F, r) <= Delta:
            # r agrees with x^p on O
            assert all(F.peval(r, a) == F.pow(a, p) for a in O)
            sec += 1
            by[w] = by.get(w, 0) + 1
    print(f"  {kind:5s} GF(2^{m}) n={n} Delta={Delta} psi=X^{p}, g={g}: dim of the code {dim}; words of the coset with "
          f"weight in [{Amin}, {p}]: {tot}; sections among them: {sec} {dict(sorted(by.items()))}")
    sys.stdout.flush()


if __name__ == "__main__":
    print("# n = 32 (Johnson radius 22.6): centre X^p, sections of agreement >= 20")
    for kind, m in (("field", 5), ("span", 10), ("rand", 10)):
        for p in (20, 21, 22, 23, 24):
            run(m, 5, kind, p, 20)
    print("# n = 64 (Johnson radius 45.3): centre X^p, sections of agreement >= 42")
    for kind, m in (("rand", 12), ("span", 12)):
        for p in (44, 45, 46, 48):
            run(m, 6, kind, p, 42)
