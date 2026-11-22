"""Note 86: numerical check of the sandwich and of the level decomposition of the deficiency on saturations of random class patterns.
For S = sat(P), M_p = meet of the two leaves, Y = R(S^meet): checks
   2 r(S^meet) + #{x : Lambda_x != M_p}  <=  r(S)  <=  2 r(S^meet) + sum_x rho_x,   rho_x = dim (U_x + Y)/Y,
that S^meet is saturated on the upper code, and records Delta = 2 r(S^meet) + sum rho - r(S) and the bound sum e_x - (two largest).
usage: 86_sandwich.py m v r count seed"""
import sys, random, itertools, collections
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
mul, rref, rank, reduce_mod, tensor, tensor_K, in_span, kernel = lib.mul, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.tensor_K, lib.in_span, lib.kernel
def span_f2(bas):
    s = {0}
    for b in bas: s |= {x ^ b for x in s}
    return s
def basis_f2(vecs):
    out = []; s = {0}
    for v in sorted(vecs):
        if v not in s: out.append(v); s |= {x ^ v for x in s}
    return out
def up_vec(vec, b, L):
    K = len(vec) // L; out = [0] * (2 * L * K)
    for a in range(L):
        for e in range(K): out[a * 2 * K + 2 * e + b] = vec[a * K + e]
    return out
def qstar(G_lo, G_hi, P, L, k):
    R, piv = rref(lib.pattern_rows(G_lo, P, L), L * k)
    inR = lambda u: in_span(R, piv, up_vec(u, 0, L)) and in_span(R, piv, up_vec(u, 1, L))
    return [[th for th in range(1, 1 << L) if inR(tensor(th, G_hi[p], L))] for p in range(len(G_hi))], R, piv
def main():
    m, v, r, count, seed = [int(a) for a in sys.argv[1:6]]; L = m - 1
    T = lib.Tree(v, r, seed); G0, G1 = T.rows(0), T.rows(1); G2 = T.rows(2) if v >= 2 else None; n = T.n; k = T.k
    rnd = random.Random(seed + 5)
    classes = ['.'] + [''.join(map(str, c)) for s in range(2, m + 1) for c in itertools.combinations(range(m), s)]
    stats = collections.Counter()
    for it in range(count):
        dens = rnd.choice([0.4, 0.6, 0.8])
        P = [lib.basis_of(rnd.choice(classes[1:])) if rnd.random() < dens else [] for _ in range(n)]
        Qs, R, piv = qstar(G0, G1, P, L, k)
        S = [basis_f2(span_f2(P[x]) | span_f2(P[x] + Qs[x >> 1])) for x in range(n)]
        rS = rank(lib.pattern_rows(G0, S, L)); assert rS == len(piv)
        Mt = [basis_f2(span_f2(S[2 * p]) & span_f2(S[2 * p + 1])) for p in range(n // 2)]
        assert all(span_f2(Mt[p]) == span_f2(Qs[p]) for p in range(n // 2)), 'meet of the saturation is not Q*'
        Yr, Yp = rref(lib.pattern_rows(G1, Mt, L), L * k // 2) if any(Mt) else ([], [])
        rho = [rank([reduce_mod(Yr, Yp, tensor(th, G1[x >> 1], L)) for th in S[x]]) if S[x] else 0 for x in range(n)]
        nact = sum(1 for x in range(n) if len(S[x]) > len(Mt[x >> 1]))
        lo, hi = 2 * len(Yp) + nact, 2 * len(Yp) + sum(rho)
        assert lo <= rS <= hi, ('SANDWICH FAILS', lo, rS, hi)
        if G2 is not None:  # the meet pattern is saturated one level up
            Q2, _, _ = qstar(G1, G2, Mt, L, k // 2)
            assert all(span_f2(Q2[u]) <= (span_f2(Mt[2 * u]) & span_f2(Mt[2 * u + 1])) for u in range(n // 4)), 'meet pattern not saturated'
        stats[('Delta', hi - rS)] += 1; stats[('r - lower', rS - lo)] += 1
    for key, c in sorted(stats.items()): print(' ', key, c)
    print('all', count, 'saturated patterns satisfy the sandwich; meet patterns saturated')
main()
