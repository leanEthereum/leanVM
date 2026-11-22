"""Note 86: on three-member patterns that violate (C*), check the description of the upper object at the level of birth:
Y_2 (the rational full part two levels up) = R(Q2 + a) cap R(Q2 + b), Q2 the binary part of Y_2 and a, b the two nodes with a line that is not binary,
and dim Y_2 = r(Q2 + a) + r(Q2 + b) - r(Q2 + a + b) = r(Q2) + 1.
usage: 86_birth.py v r patterns.txt [seed]"""
import sys, random
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib'); ch = importlib.import_module('86_chain_lib')
rref, rank, tensor, tensor_K, in_span, kernel, mul = lib.rref, lib.rank, lib.tensor, lib.tensor_K, lib.in_span, lib.kernel, lib.mul
L = 2
def main():
    v, r, fn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    T = lib.Tree(v, r, seed); G2 = T.rows(2); K2 = T.dim(2); tot = ok = 0
    for line in open(fn):
        P = line.split('|')[0].split()
        if len(P) != T.n: continue
        X2 = ch.chain(T, P, L, 2, random.Random(seed + 77))
        Y2 = [tensor_K(nu, G2[u]) for u in range(len(G2)) for nu in X2[u]]; Yr, Yp = rref(Y2, L * K2)
        Q2 = []; nb = []
        for u in range(len(G2)):
            R_, p_ = rref(X2[u], L) if X2[u] else ([], [])
            bins = [th for th in (1, 2, 3) if X2[u] and in_span(R_, p_, [(th >> a) & 1 for a in range(L)])]
            Q2.append({0: [], 1: bins[:1], 3: [1, 2]}[len(bins)])
            if len(X2[u]) > len(Q2[-1]): nb.append(u)
        tot += 1
        def rows(extra): return lib.pattern_rows(G2, [([1, 2] if u in extra else Q2[u]) for u in range(len(G2))], L)
        import itertools
        good = False
        for a, b in itertools.combinations(nb, 2):
            rq, ra, rb, rab = rank(rows([])), rank(rows([a])), rank(rows([b])), rank(rows([a, b]))
            Ra, pa = rref(rows([a]), L * K2); Rb, pb = rref(rows([b]), L * K2)
            inside = all(in_span(Ra, pa, y) and in_span(Rb, pb, y) for y in Yr)
            if inside and len(Yp) == ra + rb - rab:
                good = True
                print('dim Y_2 =', len(Yp), '| nodes with a non-binary line', nb, 'a, b =', a, b, '| r(Q2) =', rq, 'r(Q2+a) =', ra, 'r(Q2+b) =', rb, 'r(Q2+a+b) =', rab); break
        if not good: print('dim Y_2 =', len(Yp), 'nodes with a non-binary line', nb, ' <-- NOT an intersection R(Q2+a) cap R(Q2+b)')
        ok += good
    print('patterns', tot, '; Y_2 = R(Q2+a) cap R(Q2+b) for two nodes a, b on', ok)
main()
