#!/usr/bin/env python3
"""Note 48, Lemma F (anisotropic support of the Y1-coefficients of an element of the contact ideal).

For a prime p and (m, b): V = { Q in F_p[T, S, Y1] : deg_{Y1} Q <= b, deg_{(T,S)} Q <= m + 2, Q in c_m },
c_m = span{ T^i w^l Y1^e : i + 2l >= m }, w = S - T Y1. V is computed from the definition (re-expansion in the
basis T^i w^l Y1^e, no use of the lemma). Claim tested: the monomials T^r S^q Y1^c that occur in some element
of V are exactly those with
      r + q >= m - b     and     2r + q >= m - (b - c)        (or r + q >= m),
in particular the leading coefficient Q_b is supported on 2r + q >= m, so Q_b(0, S) is divisible by S^m.
Run: python3 48_fibre.py     (p = 2, 3, 5; m <= 9, b <= 4; about 20 s)
"""
import sys
from math import comb


def nullspace_mod(rows, ncols, p):
    """rows: list of dicts col -> value mod p. Returns a basis of the nullspace as lists of length ncols."""
    piv = {}          # pivot col -> row (dict), normalized
    for r in rows:
        r = dict(r)
        while r:
            c = min(r)
            if c in piv:
                f = r[c]
                pr = piv[c]
                for k, v in pr.items():
                    nv = (r.get(k, 0) - f * v) % p
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
            else:
                inv = pow(r[c], p - 2, p)
                r = {k: v * inv % p for k, v in r.items()}
                piv[c] = r
                break
    # back-substitute: free columns
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    # reduce pivot rows fully (so that each pivot row only has its pivot and free columns)
    for c in sorted(piv, reverse=True):
        r = piv[c]
        for k in [k for k in r if k != c and k in piv]:
            f = r[k]
            for kk, v in piv[k].items():
                nv = (r.get(kk, 0) - f * v) % p
                if nv:
                    r[kk] = nv
                else:
                    r.pop(kk, None)
    for fc in free:
        vec = [0] * ncols
        vec[fc] = 1
        for c, r in piv.items():
            if fc in r:
                vec[c] = (-r[fc]) % p
        basis.append(vec)
    return basis


def run(p, m, b):
    D = m + 2
    mons = [(r, q, c) for c in range(b + 1) for r in range(D + 1) for q in range(D + 1 - r)]
    idx = {mn: i for i, mn in enumerate(mons)}
    # T^r S^q Y1^c = sum_k C(q, k) T^(r+k) w^(q-k) Y1^(c+k); condition: coefficient of T^i w^l Y1^e is 0 when i + 2l < m
    rows = {}
    for (r, q, c) in mons:
        for k in range(q + 1):
            co = comb(q, k) % p
            if not co:
                continue
            i, l, e = r + k, q - k, c + k
            if i + 2 * l < m:
                rows.setdefault((i, l, e), {})[idx[(r, q, c)]] = co
    basis = nullspace_mod(list(rows.values()), len(mons), p)
    occurs = set()
    for v in basis:
        for i, x in enumerate(v):
            if x:
                occurs.add(mons[i])
    pred = set()
    for (r, q, c) in mons:
        if r + q >= m or (r + q >= m - b and 2 * r + q >= m - (b - c)):
            pred.add((r, q, c))
    extra = occurs - pred          # would refute the lemma
    missing = pred - occurs        # the lemma would not be sharp
    return len(basis), extra, missing


if __name__ == "__main__":
    bad = 0
    lead_missing = 0
    for p in (2, 3, 5):
        for m in range(1, 10):
            for b in range(0, 5):
                dim, extra, missing = run(p, m, b)
                if extra:
                    bad += 1
                lead_missing += sum(1 for t in missing if t[2] == b)
                tag = "OK" if not extra else f"VIOLATION {sorted(extra)[:5]}"
                sharp = "sharp" if not missing else f"not sharp ({len(missing)} predicted monomials never occur, e.g. {sorted(missing)[:3]})"
                if extra or (m in (4, 6, 8) and b in (1, 2)):
                    print(f"p = {p}, m = {m}, b = {b}: dim V = {dim}, support {tag}, {sharp}")
    print(f"violations of Lemma F: {bad} (p in 2, 3, 5; m = 1..9; b = 0..4)")
    print(f"monomials of the predicted support of the LEADING coefficient that never occur: {lead_missing} (0 means the support is exact)")
