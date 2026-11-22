#!/usr/bin/env python3
"""Structural checks for 40-rate-half-residual.md, over GF(2) (the contact ideal at a point is defined
over the prime field after translating the point to the origin).

  A  Lemma N: a polynomial Q(T, S, Y1) of Y1-degree <= b in the contact ideal c_m has every Y1-coefficient
     in (T, S)^(m - b); and the rank of the conditions on the rectangle is R(m, b).
  B  first integrals with b = 1: dE = E_T + Y1 E_S lies in c_(2j) iff E is in F[T^2, S^2] + (T, S)^(2j).
  C  contact orders add: o(Q^2) = 2 o(Q) on random Q (inseparable components).
Run: python3 40_checks.py   (a few seconds)
"""
import random
from itertools import product

from importlib import import_module

lib = import_module("40_lib")


def binom2(a, b):
    return 1 if (b & ~a) == 0 and b <= a else 0


def to_Tw(poly):
    """poly: dict (r, q, e) -> 1 for T^r S^q Y1^e over GF(2); substitute S = w + T Y1.
    Returns the set of (i, l, f) with odd coefficient of T^i w^l Y1^f."""
    out = set()
    for (r, q, e) in poly:
        for p in range(q + 1):
            if binom2(q, p):
                key = (r + p, q - p, e + p)
                if key in out:
                    out.remove(key)
                else:
                    out.add(key)
    return out


def contact_order(poly):
    tw = to_Tw(poly)
    return min((i + 2 * l for (i, l, f) in tw), default=10 ** 9)


def gf2_nullspace(rows, ncols):
    """rows: list of ints (bit c = column c). Returns basis of the null space as ints."""
    piv = {}
    for r in rows:
        while r:
            c = r.bit_length() - 1
            if c in piv:
                r ^= piv[c]
            else:
                piv[c] = r
                break
    # back-substitute to reduced form
    cols = sorted(piv)
    for c in cols:
        for c2 in cols:
            if c2 != c and (piv[c2] >> c) & 1:
                piv[c2] ^= piv[c]
    basis = []
    for f in range(ncols):
        if f in piv:
            continue
        x = 1 << f
        for c in cols:
            if (piv[c] >> f) & 1:
                x |= 1 << c
        basis.append(x)
    return basis, len(piv)


def check_A():
    print("A. Lemma N: Q in c_m with deg_Y1 Q <= b  =>  every Y1-coefficient in (T,S)^(m-b)")
    for m in range(1, 9):
        for b in range(0, m + 1):
            dmax = m + 2
            monos = [(r, q, e) for r in range(dmax + 1) for q in range(dmax + 1 - r) for e in range(b + 1)]
            idx = {mo: i for i, mo in enumerate(monos)}
            # linear conditions: coefficient of T^i w^l Y1^f with i + 2l < m
            conds = {}
            for mo in monos:
                for key in to_Tw({mo: 1}):
                    if key[0] + 2 * key[1] < m:
                        conds[key] = conds.get(key, 0) | (1 << idx[mo])
            basis, rk = gf2_nullspace(list(conds.values()), len(monos))
            worst = 10 ** 9
            for x in basis:
                for i, mo in enumerate(monos):
                    if (x >> i) & 1:
                        worst = min(worst, mo[0] + mo[1])
            # rank on the rectangle {r + q < m}
            rect = [i for i, mo in enumerate(monos) if mo[0] + mo[1] < m]
            mask = sum(1 << i for i in rect)
            _, rk_rect = gf2_nullspace([c & mask for c in conds.values()], len(monos))
            ok = worst >= m - b and rk_rect == lib.Rloc(m, b)
            assert ok, (m, b, worst, rk_rect, lib.Rloc(m, b))
    print("   ok for 1 <= m <= 8, 0 <= b <= m: lowest (T,S)-degree in the kernel is >= m - b; rank = R(m, b)")


def check_B():
    print("B. b = 1: dE in c_(2j)  <=>  E in F[T^2,S^2] + (T,S)^(2j)")
    for j in (1, 2, 3):
        d = 2 * j + 3
        monos = [(r, q) for r in range(d + 1) for q in range(d + 1 - r)]
        idx = {mo: i for i, mo in enumerate(monos)}
        conds = {}
        for (r, q) in monos:
            dE = {}
            if r & 1:
                dE[(r - 1, q, 0)] = 1
            if q & 1:
                dE[(r, q - 1, 1)] = 1
            for key in to_Tw(dE):
                if key[0] + 2 * key[1] < 2 * j:
                    conds[key] = conds.get(key, 0) ^ (1 << idx[(r, q)])
        basis, rk = gf2_nullspace(list(conds.values()), len(monos))
        bad = set(lib.contact_conditions(j))
        assert rk == len(bad), (j, rk, len(bad))
        for x in basis:
            for i, mo in enumerate(monos):
                if (x >> i) & 1:
                    assert mo not in bad
        print(f"   j = {j}: the kernel is spanned by the monomials outside the {len(bad)} conditions "
              f"(3j^2+j)/2 = {(3*j*j+j)//2}")


def check_C():
    print("C. o(Q^2) = 2 o(Q) for random Q (orders add in the contact filtration)")
    rng = random.Random(7)
    for _ in range(200):
        Q = {}
        for _ in range(rng.randrange(1, 8)):
            Q[(rng.randrange(4), rng.randrange(4), rng.randrange(3))] = 1
        # make Q vanish at the origin with some probability
        o1 = contact_order(Q)
        if o1 > 100:
            continue
        Q2 = {}
        keys = list(Q)
        for a in keys:
            key = (2 * a[0], 2 * a[1], 2 * a[2])
            Q2[key] = 1
        assert contact_order(Q2) == 2 * o1
    print("   ok on 200 random Q over GF(2)")


if __name__ == "__main__":
    check_A()
    check_B()
    check_C()
