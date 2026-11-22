"""Researcher 05: the second coefficient c(V) of a subspace polynomial, its dual formula, and its fibers.

For V a subspace of D of dimension k, L_V = X^(2^k) + c(V) X^(2^(k-1)) + ... . Checks:
  1. the dual space: alpha_phi := delta_H^(-2) (H = ker phi, delta_H = L_H(u), u not in H) is additive in phi;
  2. c(V)^(2^(r+1)) = d^2 + sum_{alpha in A_V, alpha != 0} 1/alpha, with r = codim V, d the second coefficient of L_D
     and A_V = {alpha_phi : phi vanishes on V};
  3. fibers of c on codimension-2 subspaces: exhaustive in GF(2^16) (N = 8) against the birthday expectation, and in
     the real K = GF(2^64) for N = 12 (2.8 million subspaces; expected: all distinct);
  4. the real domain N = 25 in K: the dual space is not closed under multiplication by any element of GF(256) minus GF(2)
     (no subfield structure that would make inverse sums cancel);
  5. the structural collisions of c in the real K: for N = 8..11 exactly one pair of codimension-2 subspaces shares
     c (printed as functionals on the coefficients), and three pairs in codimension 3 (N = 8, 9);
  6. the pigeonhole mechanism in a small field: GF(2^8), N = 7, codimension 3: the largest fiber of c gives a list at
     agreement 4K - 1 for rate 1/32 (verified by evaluation).
Run: python3 05_check_flat_tops.py   (about two minutes)
"""
import random
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import importlib

gfm = importlib.import_module("05_gf")
GF, span, subspaces_by_codim, kernel_basis, parity, rank_reduce = (
    gfm.GF, gfm.span, gfm.subspaces_by_codim, gfm.kernel_basis, gfm.parity, gfm.rank_reduce)


def dual_basis(F, N):
    """alpha_i = delta_{H_i}^(-2) for the coordinate functionals phi_i (H_i = span of x^j, j != i)."""
    out = []
    for i in range(N):
        LH = F.subspace_poly([1 << j for j in range(N) if j != i])
        delta = F.lin_eval(LH, 1 << i)
        out.append(F.inv(F.sq(delta)))
    return out


def alpha_of(F, N, phi):
    """delta_H^(-2) for H = ker phi, computed directly."""
    p = phi.bit_length() - 1
    basis = []
    for i in range(N):
        if i == p:
            continue
        basis.append((1 << i) | ((1 << p) if (phi >> i) & 1 else 0))
    LH = F.subspace_poly(basis)
    delta = F.lin_eval(LH, 1 << p)
    return F.inv(F.sq(delta))


def check_dual(F, N, rng, trials=20):
    al = dual_basis(F, N)
    for _ in range(trials):
        phi = rng.randrange(1, 1 << N)
        s = 0
        for i in range(N):
            if (phi >> i) & 1:
                s ^= al[i]
        assert s == alpha_of(F, N, phi), "dual space not additive"
    print(f"GF(2^{F.m}), N={N}: phi -> delta_H^(-2) is additive ({trials} random functionals)")
    return al


def check_iota_formula(F, N, rng, trials=20):
    al = dual_basis(F, N)
    LD = F.subspace_poly([1 << j for j in range(N)])
    d = LD[N - 1]
    for r in (1, 2, 3):
        subs = subspaces_by_codim(N, r)
        for _ in range(trials):
            funcs = rng.choice(subs)
            LV = F.subspace_poly(kernel_basis(N, funcs))
            c = LV[N - r - 1]
            iota = 0
            for comb in range(1, 1 << r):
                a = 0
                for t in range(r):
                    if (comb >> t) & 1:
                        phi = funcs[t]
                        for i in range(N):
                            if (phi >> i) & 1:
                                a ^= al[i]
                iota ^= F.inv(a)
            lhs = c
            for _ in range(r + 1):
                lhs = F.sq(lhs)
            assert lhs == F.sq(d) ^ iota, "iota formula fails"
    print(f"GF(2^{F.m}), N={N}: c(V)^(2^(r+1)) = d^2 + iota(A_V) for r = 1, 2, 3 ({trials} random V each)")


def fibers_codim2(F, N):
    """Multiset of iota(A) over all 2-dimensional subspaces A of the dual space."""
    al = dual_basis(F, N)
    elems = [0] * (1 << N)
    for v in range(1, 1 << N):
        low = v & -v
        elems[v] = elems[v ^ low] ^ al[low.bit_length() - 1]
    inv = [0] + [F.inv(e) for e in elems[1:]]
    cnt = Counter()
    total = 0
    for a in range(1, 1 << N):
        ia = inv[a]
        for b in range(a + 1, 1 << N):
            c = a ^ b
            if c > b:  # a < b < a^b: each subspace once
                cnt[ia ^ inv[b] ^ inv[c]] += 1
                total += 1
    sizes = Counter(cnt.values())
    pairs = sum(v * (v - 1) // 2 for v in cnt.values())
    print(f"GF(2^{F.m}), N={N}: {total} codimension-2 subspaces, {len(cnt)} distinct values of c, fiber sizes "
          f"{dict(sorted(sizes.items()))}, colliding pairs {pairs}, birthday expectation "
          f"{total * (total - 1) / 2 / F.size:.3g}")


def structural_collisions(F):
    for N in range(8, 12):
        al = dual_basis(F, N)
        elems = [0] * (1 << N)
        for v in range(1, 1 << N):
            low = v & -v
            elems[v] = elems[v ^ low] ^ al[low.bit_length() - 1]
        inv = [0] + [F.inv(e) for e in elems[1:]]
        seen, coll = {}, []
        for a in range(1, 1 << N):
            for b in range(a + 1, 1 << N):
                c = a ^ b
                if c > b:
                    val = inv[a] ^ inv[b] ^ inv[c]
                    if val in seen:
                        coll.append((seen[val], (a, b, c)))
                    else:
                        seen[val] = (a, b, c)
        fmt = lambda t: "{" + ", ".join(bin(x)[2:].zfill(N) for x in t) + "}"
        print(f"GF(2^{F.m}), N={N}, codimension 2: collisions of c: " + "; ".join(fmt(x) + " = " + fmt(y) for x, y in coll))
        if N <= 9:
            seen3, n3 = {}, 0
            for funcs in subspaces_by_codim(N, 3):
                a, b, c = funcs
                val = inv[a] ^ inv[b] ^ inv[c] ^ inv[a ^ b] ^ inv[a ^ c] ^ inv[b ^ c] ^ inv[a ^ b ^ c]
                if val in seen3:
                    n3 += 1
                else:
                    seen3[val] = funcs
            print(f"GF(2^{F.m}), N={N}, codimension 3: {len(seen3) + n3} subspaces, {n3} colliding pairs")


def subfield_closure(F, N):
    """dim(lambda * Dhat ∩ Dhat) for lambda in GF(256) minus GF(2), Dhat the dual space of D_N, and the same for D_N."""
    al = dual_basis(F, N)
    g = F.pow(2, (F.size - 1) // 255)  # generator of GF(256)^* if x has full enough order
    assert F.pow(g, 255) == 1 and F.pow(g, 85) != 1 and F.pow(g, 51) != 1
    worst = 0
    worstD = 0
    lam = 1
    for e in range(1, 255):
        lam = F.mul(lam, g)
        rk = len(rank_reduce(al + [F.mul(lam, a) for a in al]))
        worst = max(worst, 2 * N - rk)
        dom = [1 << i for i in range(N)]
        rk = len(rank_reduce(dom + [F.mul(lam, a) for a in dom]))
        worstD = max(worstD, 2 * N - rk)
    print(f"GF(2^{F.m}), N={N}: max over lambda in GF(256) minus GF(2) of dim(lambda Dhat ∩ Dhat) = {worst}, "
          f"of dim(lambda D ∩ D) = {worstD}; rank of the dual basis = {len(rank_reduce(al))}")


def pigeonhole_demo():
    F = GF(8)
    N, r = 7, 3
    k = N - r
    Q = 1 << k
    K = Q // 4
    fib = {}
    for funcs in subspaces_by_codim(N, r):
        LV = F.subspace_poly(kernel_basis(N, funcs))
        fib.setdefault(LV[k - 1], []).append((funcs, LV))
    c, best = max(fib.items(), key=lambda kv: len(kv[1]))
    # the word w(x) = x^Q + c x^(Q/2); member V has codeword C_V = w - L_V of degree <= Q/4 = K agreeing on V, and
    # C_V / X of degree < K agreeing with w / x on V minus 0
    ok = 0
    polys = set()
    for funcs, LV in best:
        V = span(kernel_basis(N, funcs))
        assert all(cj == 0 for cj in LV[k - 1 + 1:k]) and LV[k] == 1 and LV[k - 1] == c
        low = LV[:k - 1]  # coefficients of X^(2^j), j <= k-2: degree <= Q/4
        agree = sum(1 for v in V if F.lin_eval(low, v) == (F.pow(v, Q) ^ F.mul(c, F.pow(v, Q // 2))))
        assert agree == Q
        polys.add(tuple(low))
        ok += 1
    sizes = sorted((len(v) for v in fib.values()), reverse=True)
    print(f"GF(2^8), N={N}, rate 1/{(1 << N) // K}: {sum(sizes)} subspaces of codimension {r}, {len(fib)} values of c, "
          f"largest fibers {sizes[:5]}; the largest gives {len(polys)} distinct polynomials of degree <= K = {K} "
          f"agreeing with x^{Q} + c x^{Q // 2} on {Q} = 4K points each (average fiber {sum(sizes) / F.size:.1f})")


if __name__ == "__main__":
    rng = random.Random(55)
    F16 = GF(16)
    check_dual(F16, 8, rng)
    check_iota_formula(F16, 8, rng)
    fibers_codim2(F16, 8)
    pigeonhole_demo()
    F64 = GF(64)
    check_dual(F64, 25, rng, trials=5)
    for N in (20, 22, 25, 28):
        subfield_closure(F64, N)
    structural_collisions(F64)
    fibers_codim2(F64, 12)
