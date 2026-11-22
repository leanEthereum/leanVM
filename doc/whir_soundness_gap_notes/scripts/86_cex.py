"""Note 86: the counterexample to (C*) and (C') for three members at (16, 32).
(1) rank of P at several draws; (2) the three levels of the mechanism; (3) min of B(P;Q) over all binary Q below Q* (an exact Q is below Q*).
usage: 86_cex.py [seed ...]"""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
mul, rref, rank, reduce_mod, tensor, in_span, kernel = lib.mul, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.in_span, lib.kernel
P = '012 012 012 012 02 02 02 02 012 012 . 012 . 012 . 012 12 12 12 12 . . . . . . . . 01 01 01 01'.split()
Q2 = '012 02 . . 12 . . 01'.split()
L = 2
SUB = {'.': ['.'], '01': ['.', '01'], '02': ['.', '02'], '12': ['.', '12'], '012': ['.', '01', '02', '12', '012']}
def join(a, b):
    if a == '.': return b
    if b == '.' or a == b: return a
    return '012'
def main():
    seeds = [int(s) for s in sys.argv[1:]] or [1, 2, 3]
    for seed in seeds:
        T = lib.Tree(4, 1, seed)
        G0, G1, G2 = T.rows(0), T.rows(1), T.rows(2)
        r0 = rank(lib.pattern_rows(G0, P, L))
        print('seed', seed, ': w =', lib.weight(P), ' L k =', L * T.k, ' rank of P at (16,32) =', r0)
        # level 2
        Y2, piv2 = rref(lib.pattern_rows(G2, Q2, L), L * 4)
        red = {p: [reduce_mod(Y2, piv2, tensor(th, G2[p], L)) for th in (1, 2)] for p in (2, 3)}
        print('   level 2: rank of Q2 =', len(piv2), ', dim of (K^2 g_2 + K^2 g_3) mod Y2 =', rank(red[2] + red[3]), '(two planes of a 3-space: they share a line)')
        ker = kernel([list(c) for c in zip(*(red[2] + red[3]))], 4)
        a1, a2, b1, b2 = ker[0]
        print('   common line: nu at node 2 binary?', a1 == 0 or a2 == 0 or a1 == a2, '; at node 3 binary?', b1 == 0 or b2 == 0 or b1 == b2)
        # full binary part Q* of P: theta (x) g_p (x) F^2 in R(P)
        R0, pv0 = rref(lib.pattern_rows(G0, P, L), L * 16)
        def inR(th, p):
            return all(in_span(R0, pv0, tensor(th, [y for g in G1[p] for y in ((g, 0) if b == 0 else (0, g))], L)) for b in (0, 1))
        Qs = []
        for p in range(16):
            s = [th for th in (1, 2, 3) if inR(th, p)]
            Qs.append({(): '.', (1,): '01', (2,): '02', (3,): '12', (1, 2, 3): '012'}[tuple(s)])
        print('   Q* =', ' '.join(Qs))
        cache = {}
        def up(Q):
            Q = tuple(Q)
            if Q not in cache: cache[Q] = rank(lib.pattern_rows(G1, Q, L)) if lib.weight(Q) else 0
            return cache[Q]
        def B(Q):
            base = up(Q); s = 2 * base
            for x in range(32):
                p = x >> 1; j = join(Q[p], P[x])
                if j != Q[p]: Q2_ = list(Q); Q2_[p] = j; s += up(Q2_) - base
            return s
        print('   B(P;Q*) =', B(Qs), ', B(P;0) =', B(['.'] * 16))
        if seed == seeds[0]:
            best = min((B(list(Q)), Q) for Q in itertools.product(*[SUB[c] for c in Qs]))
            print('   min of B(P;Q) over the', len(list(itertools.product(*[SUB[c] for c in Qs]))), 'binary Q below Q*:', best[0], 'at', ' '.join(best[1]))
main()
