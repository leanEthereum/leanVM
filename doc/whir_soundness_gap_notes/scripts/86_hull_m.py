"""Note 86: the one-level identity with the rational full part, any number of members.
For each class pattern: rank r, Q* (binary full part), B(P;Q*), and Y^K = sum_p Xi_p (x) g_p with Xi_p the vectors nu (constant when the
bottom twiddles are redrawn; three draws) with nu (x) g_p (x) F^2 inside R; B(P;Y^K) = 2 dim Y^K + sum_x dim (U_x + Y^K)/Y^K.
The same for the saturation of the pattern (Q*_p added to both leaves of every pair).
usage: 86_hull_m.py m v r patterns.txt [seed]"""
import sys, random, copy
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
mul, rref, rank, reduce_mod, tensor, tensor_K, in_span, kernel = lib.mul, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.tensor_K, lib.in_span, lib.kernel
def up_vec(vec, b, L):
    K = len(vec) // L; out = [0] * (2 * L * K)
    for a in range(L):
        for e in range(K): out[a * 2 * K + 2 * e + b] = vec[a * K + e]
    return out
def unit(a, L): return [1 if j == a else 0 for j in range(L)]
def analyse(P, trees, L):
    T = trees[0]; G1 = T.rows(1); n1 = T.n // 2; k = T.k
    conds = [[] for _ in range(n1)]; first = None
    for T_ in trees:
        R, piv = rref(lib.pattern_rows(T_.rows(0), P, L), L * k)
        if first is None: first = (R, piv)
        for p in range(n1):
            for b in (0, 1):
                reds = [reduce_mod(R, piv, up_vec(tensor_K(unit(a, L), G1[p]), b, L)) for a in range(L)]
                conds[p] += [[reds[a][c] for a in range(L)] for c in range(L * k)]
    R, piv = first; rk = len(piv)
    inR = lambda u: in_span(R, piv, up_vec(u, 0, L)) and in_span(R, piv, up_vec(u, 1, L))
    Qs = [[th for th in range(1, 1 << L) if inR(tensor(th, G1[p], L))] for p in range(n1)]
    Xi = [kernel(conds[p], L) for p in range(n1)]
    def Bof(Y):
        Yr, Yp = rref(Y, L * k // 2) if Y else ([], [])
        s = 2 * len(Yp)
        for x, tok in enumerate(P):
            bas = lib.basis_of(tok)
            if bas: s += rank([reduce_mod(Yr, Yp, tensor(th, G1[x >> 1], L)) for th in bas])
        return s, len(Yp)
    Bs, dS = Bof([tensor(th, G1[p], L) for p in range(n1) for th in Qs[p]])
    BK, dK = Bof([tensor_K(nu, G1[p]) for p in range(n1) for nu in Xi[p]])
    nonbin = [p for p in range(n1) if len(Xi[p]) > len(lib.rref([[(th >> a) & 1 for a in range(L)] for th in Qs[p]], L)[1] if Qs[p] else [])]
    return rk, Bs, dS, BK, dK, nonbin, Qs
def main():
    m, v, r, fn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]; seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    L = m - 1; T = lib.Tree(v, r, seed); trees = [T]; rnd = random.Random(seed + 1000)
    for _ in range(2):
        T2 = copy.deepcopy(T); T2.tw[0] = [lib.rnd_elt(rnd) for _ in T2.tw[0]]; trees.append(T2)
    bad = 0; tot = 0
    for line in open(fn):
        P = line.split('|')[0].split()
        if len(P) != T.n: continue
        for label in ('pattern   ', 'saturation'):
            rk, Bs, dS, BK, dK, nonbin, Qs = analyse(P, trees, L)
            print(label, 'w', lib.weight(P), 'rank', rk, '| B(P;Q*)', Bs, 'dim Y*', dS, '| B(P;Y^K)', BK, 'dim Y^K', dK, '| pairs with a non-binary rational functional:', nonbin, '' if BK == rk else ' <-- IDENTITY FAILS')
            tot += 1; bad += BK != rk
            P = [lib.basis_of(tok) + Qs[x >> 1] for x, tok in enumerate(P)]
            P = [[th for th in range(1, 1 << L) if in_f2_span(th, bas)] for bas in P]; P = [f2_basis(s) for s in P]
    print('systems', tot, '; identity with the rational full part fails on', bad)
def in_f2_span(v, bas):
    span = {0}
    for b in bas: span |= {s ^ b for s in span}
    return v in span
def f2_basis(vecs):
    out = []; span = {0}
    for v in vecs:
        if v not in span: out.append(v); span |= {s ^ v for s in span}
    return out
main()
