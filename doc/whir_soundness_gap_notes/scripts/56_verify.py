#!/usr/bin/env python3
"""Researcher 56. Direct verification, at the real sizes, of the pairs (A, B) given by the six-point words that
`56_struct N 64 0x1b` prints (56-witt-real-field.md, Section 5.2): deg(Z_A - Z_B) = 0 in K = GF(2^64) =
F_2[x] / (x^64 + x^4 + x^3 + x + 1), on D = span(1, x, .., x^(N-1)).

For a word phi_1..phi_6 and signs eps (odd number of minus signs), c = (1/4) sum eps_i (-1)^phi_i takes the
values 0, 1, -1 and is constant on the cosets of W = the common kernel of the phi_i (codimension rho = 4 or 5).
A = {c = 1} and B = {c = -1} are unions of 3 * 2^rho / 16 cosets t + W, and Z_(t + W)(X) = L_W(X) - L_W(t), so
    Z_A = P_A(L_W(X)),  Z_B = P_B(L_W(X)),  P_A(Y) = prod over the cosets of A of (Y - L_W(t)),
identically. The script computes the labels L_W(t) in K (subspace polynomial of the 2^(N - rho) points of W,
evaluated through a basis), multiplies out P_A and P_B (degree 3 or 6) and checks that they differ exactly in
their constant terms. This is the degree of Z_A - Z_B itself, not the dual criterion: no theorem of note 19 is
used. All 16 pairs of every word are checked.
usage: 56_verify.py N words.txt [N words.txt ...]"""
import sys

MOD_TAIL = 0x1B
MASK = (1 << 64) - 1


def mul(a, b):
    r = 0
    while b:
        low = b & -b
        r ^= a << (low.bit_length() - 1)
        b ^= low
    # reduce modulo x^64 + x^4 + x^3 + x + 1
    for _ in range(2):
        hi = r >> 64
        if not hi:
            break
        r = (r & MASK) ^ hi ^ (hi << 1) ^ (hi << 3) ^ (hi << 4)
    return r


def kernel_basis(phis, N):
    """Basis of {x in F_2^N : popcount(phi & x) even for all phi}, and the rank of the phis."""
    ech = []                                   # (pivot bit, vector)
    for phi in phis:
        v = phi
        for b, w in ech:
            if v >> b & 1:
                v ^= w
        if v:
            b = v.bit_length() - 1
            ech = [(bb, ww ^ v if ww >> b & 1 else ww) for bb, ww in ech] + [(b, v)]
    pivots = {b: w for b, w in ech}
    free = [i for i in range(N) if i not in pivots]
    basis = []
    for f in free:
        x = 1 << f
        for b, w in pivots.items():
            if w >> f & 1:
                x |= 1 << b
        basis.append(x)
    for x in basis:
        assert all(bin(phi & x).count("1") % 2 == 0 for phi in phis)
    return basis, len(ech)


def subspace_eval(basis, zs):
    """Values L_V(z) of the subspace polynomial of V = span(basis) at the points zs."""
    v = list(basis)
    zs = list(zs)
    for i in range(len(v)):
        p = v[i]
        assert p, "dependent basis"
        for j in range(i + 1, len(v)):
            v[j] = mul(v[j], v[j] ^ p)
        zs = [mul(z, z ^ p) for z in zs]
    return zs


def poly_from_roots(roots):
    p = [1]
    for r in roots:
        q = [0] * (len(p) + 1)
        for i, a in enumerate(p):
            q[i + 1] ^= a
            q[i] ^= mul(a, r)
        p = q
    return p


def verify(N, words):
    n = 1 << N
    pairs = 0
    for w in words:
        x = 0
        for phi in w:
            x ^= phi
        assert x == 0 and len(set(w)) == 6
        wb, rho = kernel_basis(w, N)
        assert len(wb) == N - rho and rho in (4, 5)
        # coset representatives: one point for every value of (phi_1(t), .., phi_6(t))
        reps = {}
        frontier = [0]
        reps[tuple(0 for _ in w)] = 0
        for i in range(N):
            if len(reps) == 1 << rho:
                break
            e = 1 << i
            new = {}
            for pat, t in reps.items():
                t2 = t ^ e
                pat2 = tuple(bin(phi & t2).count("1") & 1 for phi in w)
                if pat2 not in reps and pat2 not in new:
                    new[pat2] = t2
            reps.update(new)
        assert len(reps) == 1 << rho
        pats = list(reps)
        labels = dict(zip(pats, subspace_eval(wb, [reps[p] for p in pats])))   # the element of D is the mask
        assert len(set(labels.values())) == 1 << rho
        seen = set()
        for signs in range(64):
            if bin(signs).count("1") % 2 == 0:
                continue
            A, B = [], []
            for pat in pats:
                s = sum(-1 if ((signs >> i & 1) ^ pat[i]) else 1 for i in range(6))
                assert s in (0, 4, -4)
                if s == 4:
                    A.append(labels[pat])
                elif s == -4:
                    B.append(labels[pat])
            assert len(A) == len(B) == 3 * (1 << rho) // 16 and not set(A) & set(B)
            key = (frozenset(A), frozenset(B))
            if (key[1], key[0]) in seen:
                continue
            seen.add(key)
            pa, pb = poly_from_roots(A), poly_from_roots(B)
            assert pa[1:] == pb[1:] and pa[0] != pb[0], (N, w, signs)
            pairs += 1
        assert len(seen) == 16
    print(f"N = {N} (n = 2^{N}, sets of 3n/16 = {3 * n // 16} points): {len(words)} words, {pairs} pairs (A, B) "
          f"verified: Z_A - Z_B is a nonzero constant in GF(2^64)")


def main():
    args = sys.argv[1:]
    for i in range(0, len(args), 2):
        N = int(args[i])
        words = []
        for line in open(args[i + 1]):
            if line.strip().startswith("word"):
                words.append([int(p, 16) for p in line.split(":")[1].split("[")[0].split()])
        verify(N, words)


if __name__ == "__main__":
    main()
