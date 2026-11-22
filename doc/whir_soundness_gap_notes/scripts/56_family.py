#!/usr/bin/env python3
"""Researcher 56. Star families built from the structural six-point words of the power shape
(56-witt-real-field.md, Section 5.3).

Input: the output of `56_struct N m r` (the words, as masks of functionals). Every word and every sign pattern
with an odd number of minus signs gives c = (1/4) sum eps_i chi_phi_i = 1_A - 1_B with |A| = |B| = 3n/16 and
Z_A - Z_B constant. All these c are functions of the 11 functionals spanning Phi, so the computation is done on
the quotient Y = F_2^11 (2048 points, each standing for n / 2048 points of D). Two differences are compatible when
A_i is disjoint from B_j and A_j from B_i. For a clique J and any set S containing every B_j and disjoint from
every A_j, the sets S and S + c_j (j in J) pairwise share their top to depth 3n/16 - 1 (the differences are
products of the units Lambda_{c_j}). The script lists the largest cliques under the size constraints of each
window: |union B| <= p <= n - |union A|.

With the argument "verify" two of the families are then checked directly in K = GF(2^64) on the real domain
D = span(1, x, .., x^(N-1)): every member S is a union of cosets of W' = the common kernel of Phi, so
Z_S = P_S(L_W'(X)) with P_S(Y) = prod over the cosets of (Y - L_W'(t)), and the script multiplies out the top
3 * 2^11 / 16 coefficients of every P_S: the members agree in the first 383 of them, which is a common top of the
Z_S to depth 3n/16 - 1, and not all agree in the next one.
usage: 56_family.py N words.txt [verify]"""
import sys

MASK = (1 << 64) - 1


def mul(a, b):
    """GF(2^64) = F_2[x] / (x^64 + x^4 + x^3 + x + 1)."""
    r = 0
    while b:
        low = b & -b
        r ^= a << (low.bit_length() - 1)
        b ^= low
    for _ in range(2):
        hi = r >> 64
        if not hi:
            break
        r = (r & MASK) ^ hi ^ (hi << 1) ^ (hi << 3) ^ (hi << 4)
    return r


def subspace_eval(basis, zs):
    v = list(basis)
    zs = list(zs)
    for i in range(len(v)):
        p = v[i]
        for j in range(i + 1, len(v)):
            v[j] = mul(v[j], v[j] ^ p)
        zs = [mul(z, z ^ p) for z in zs]
    return zs


def top_coefficients(labels, G):
    """prod (1 + lambda X) modulo X^(G+1): e_0..e_G of the label set."""
    e = [0] * (G + 1)
    e[0] = 1
    for d, lam in enumerate(labels):
        for j in range(min(d + 1, G), 0, -1):
            if e[j - 1]:
                e[j] ^= mul(lam, e[j - 1])
    return e


def main():
    N = int(sys.argv[1])
    words = []
    for line in open(sys.argv[2]):
        if line.strip().startswith("word"):
            words.append([int(p, 16) for p in line.split(":")[1].split("[")[0].split()])
    allm = (1 << N) - 1
    even = sum(1 << i for i in range(N) if i % 2 == 0)
    q4 = sum(1 << i for i in range(N) if i % 4 < 2)
    p30 = sum(1 << i for i in range(N) if i % 3 == 0)
    p31 = sum(1 << i for i in range(N) if i % 3 == 1)
    gens = [1, 2, 4, 1 << (N - 1), 1 << (N - 2), 1 << (N - 3), allm, even, q4, p30, p31]
    ech = {}
    kept = 0
    kept_gens = []
    for g in gens:
        v, c = g, 1 << kept
        while v:
            b = v.bit_length() - 1
            if b in ech:
                v ^= ech[b][0]
                c ^= ech[b][1]
            else:
                ech[b] = (v, c)
                kept += 1
                kept_gens.append(g)
                break

    def coords(mask):
        v, c = mask, 0
        while v:
            b = v.bit_length() - 1
            v ^= ech[b][0]
            c ^= ech[b][1]
        return c

    K = kept
    Y = 1 << K

    par = [bin(i).count("1") & 1 for i in range(Y)]
    cs = []
    for wi, w in enumerate(words):
        cw = [coords(m) for m in w]
        x = 0
        for c in cw:
            x ^= c
        assert x == 0 and len(set(cw)) == 6
        for signs in range(64):
            if bin(signs).count("1") % 2 == 0:
                continue
            A = B = 0
            for y in range(Y):
                s = sum(-1 if ((signs >> i & 1) ^ par[cw[i] & y]) else 1 for i in range(6))
                assert s in (0, 4, -4)
                if s == 4:
                    A |= 1 << y
                elif s == -4:
                    B |= 1 << y
            assert bin(A).count("1") == bin(B).count("1") == 3 * Y // 16
            cs.append((wi, signs, A, B))
    n = len(cs)
    print(f"N = {N}: {len(words)} words, {n} signed differences 1_A - 1_B on the quotient F_2^{K}")
    adj = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if cs[i][2] & cs[j][3] == 0 and cs[j][2] & cs[i][3] == 0:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    print("  compatible pairs:", sum(bin(a).count("1") for a in adj) // 2)

    def constrained(amax, bmax):
        best = [0, None]

        def rec(R, P, UA, UB):
            if len(R) > best[0]:
                best[0] = len(R)
                best[1] = (list(R), bin(UA).count("1") / Y, bin(UB).count("1") / Y)
            if len(R) + bin(P).count("1") <= best[0]:
                return
            while P:
                v = (P & -P).bit_length() - 1
                P &= P - 1
                ua, ub = UA | cs[v][2], UB | cs[v][3]
                if bin(ua).count("1") <= amax * Y and bin(ub).count("1") <= bmax * Y:
                    rec(R + [v], P & adj[v], ua, ub)

        rec([], (1 << n) - 1, 0, 0)
        return best

    cases = ((1.0, 1.0, "no size constraint"),
             (0.375, 0.6875, "rate 1/2, p in [5n/8, 11n/16]"),
             (0.34, 0.6875, "rate 1/2, p in [0.66 n, 11n/16]"),
             (0.5625, 0.4375, "rate 1/4, p = 7n/16"),
             (0.6875, 0.3125, "rate 1/8, p in (n/4, 5n/16]"),
             (0.75, 0.25, "rate 1/16, p in [3n/16, n/4]"))
    found = {}
    for amax, bmax, label in cases:
        b = constrained(amax, bmax)
        if b[1]:
            R, ua, ub = b[1]
            found[label] = R
            print(f"  {label}: {b[0] + 1} sets (clique of {b[0]}), |union B| = {ub:.4f} n <= p <= "
                  f"{1 - ua:.4f} n, words {sorted(set(cs[v][0] + 1 for v in R))}")
        else:
            print(f"  {label}: none")
    if len(sys.argv) > 3 and sys.argv[3] == "verify":
        verify(N, K, kept_gens, cs, found)


def verify(N, K, kept_gens, cs, found):
    Y = 1 << K
    # the point of D with generator values y: solve gen_i(x) = y_i; D is identified with the masks x
    piv = []                                     # (pivot bit, generator mask reduced, combination of generators)
    for gi, g in enumerate(kept_gens):
        v, c = g, 1 << gi
        for b, w, cw in piv:
            if v >> b & 1:
                v ^= w
                c ^= cw
        b = v.bit_length() - 1
        piv = [(bb, ww ^ v, cc ^ c) if ww >> b & 1 else (bb, ww, cc) for bb, ww, cc in piv] + [(b, v, c)]
    # after full reduction the vector e_b (bit b alone) has value 1 exactly on the combination cw of generators
    # that became the reduced row; invert: t_i with gen_j(t_i) = [i = j]
    def gen_values(x):
        r = 0
        for gi, g in enumerate(kept_gens):
            r |= (bin(g & x).count("1") & 1) << gi
        return r
    cand = [1 << b for b, _, _ in piv]
    vals = [gen_values(x) for x in cand]
    dual = []
    for i in range(K):                            # solve sum_j a_j vals[j] = e_i over F_2
        rows = [(vals[j], 1 << j) for j in range(K)]
        target, combo = 1 << i, 0
        used = []
        for bit in range(K):
            p = next((r for r in rows if r[0] >> bit & 1), None)
            assert p is not None
            rows.remove(p)
            rows = [(a ^ p[0], c ^ p[1]) if a >> bit & 1 else (a, c) for a, c in rows]
            used = [(a ^ p[0], c ^ p[1]) if a >> bit & 1 else (a, c) for a, c in used] + [p]
        for a, c in used:
            if a == target:
                combo = c
        x = 0
        for j in range(K):
            if combo >> j & 1:
                x ^= cand[j]
        assert gen_values(x) == 1 << i
        dual.append(x)
    reps = [0] * Y
    for y in range(1, Y):
        low = y & -y
        reps[y] = reps[y ^ low] ^ dual[low.bit_length() - 1]
    # basis of W' = common kernel of the generators
    pivbits = {b for b, _, _ in piv}
    wb = []
    for f in range(N):
        if f in pivbits:
            continue
        x = 1 << f
        for b, w, _ in piv:
            if w >> f & 1:
                x |= 1 << b
        assert gen_values(x) == 0
        wb.append(x)
    assert len(wb) == N - K
    labels = subspace_eval(wb, reps)
    assert len(set(labels)) == Y
    G = 3 * Y // 16
    print(f"  direct verification in GF(2^64), N = {N}: labels L_W'(t) of the {Y} cosets of W' (dimension {N - K})")
    for label, pfrac in (("rate 1/2, p in [0.66 n, 11n/16]", 11 / 16), ("rate 1/4, p = 7n/16", 7 / 16)):
        R = found[label]
        UA = UB = 0
        for v in R:
            UA |= cs[v][2]
            UB |= cs[v][3]
        size = int(pfrac * Y)
        S = UB
        y = 0
        while bin(S).count("1") < size:           # pad with the lowest points outside union A
            if not (UA | S) >> y & 1:
                S |= 1 << y
            y += 1
        members = [S] + [(S & ~cs[v][3]) | cs[v][2] for v in R]
        assert all(bin(m).count("1") == size for m in members) and len(set(members)) == len(members)
        tops = [top_coefficients([labels[y] for y in range(Y) if m >> y & 1], G) for m in members]
        agree = min(next((j for j in range(1, G + 1) if tops[i][j] != tops[0][j]), G + 1) for i in range(1, len(tops)))
        allagree = max(next((j for j in range(1, G + 1) if tops[i][j] != tops[0][j]), G + 1) for i in range(1, len(tops)))
        assert agree == G
        print(f"    {label}: {len(members)} sets of {size} cosets ({pfrac} n points); the coefficients e_1..e_{G - 1} of "
              f"P_S agree for all of them and e_{G} does not (first difference from the base set between {agree} and "
              f"{allagree}): deg(Z_S - Z_S') <= p - 3n/16 for every pair")


if __name__ == "__main__":
    main()
