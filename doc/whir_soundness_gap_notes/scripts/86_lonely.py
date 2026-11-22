"""Note 86, experiment A: geometry of the planes U_p = K^2 (x) g_p modulo Y = R(Q) for a three-member pattern Q
on the code of height 1, and the circuits of the lonely system sum_{p in J} U_p (x) z_p (generic z_p).

usage: 86_lonely.py v r count seed [verbose]      (v, r: the code that carries Q, e.g. 2 1 for (4, 8))
For every minimal set J of zero nodes of Q whose lonely system is not a direct sum, prints the ranks rho_p,
the dimension of the sum of the planes, and the binary pure tensors theta (x) g_p' (x) F^2 that lie in R but not in Y (x) F^2.
"""
import sys, random, itertools, collections
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
from importlib import import_module
mul, rref, rank, reduce_mod, tensor, in_span = lib.mul, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.in_span

def main():
    v, r, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    verbose = len(sys.argv) > 5
    T = lib.Tree(v, r, seed); G = T.rows(0); n = T.n; k = T.k; L = 2
    rnd = random.Random(seed * 7919 + 1)
    toks = ['.', '01', '02', '12', '012']
    stats = collections.Counter()
    for it in range(count):
        # structured draw: mostly doubled or sparse patterns so that kernels are not trivial
        dens = rnd.choice([0.3, 0.5, 0.7])
        Q = [rnd.choice(toks[1:]) if rnd.random() < dens else '.' for _ in range(n)]
        Y, piv = rref(lib.pattern_rows(G, Q, L), L * k) if lib.weight(Q) else ([], [])
        dimV = L * k - len(piv)
        if dimV == 0: continue
        zero = [p for p in range(n) if Q[p] == '.']
        red = {p: [reduce_mod(Y, piv, tensor(th, G[p], L)) for th in (1, 2)] for p in zero}
        rho = {p: rank(red[p]) for p in zero}
        zs = {p: (lib.rnd_elt(rnd), lib.rnd_elt(rnd)) for p in range(n)}
        def lonely_rows(J):
            rows = []
            for p in J:
                for vec in red[p]:
                    rows.append([mul(c, zs[p][0]) if c else 0 for c in vec] + [mul(c, zs[p][1]) if c else 0 for c in vec])
            return rows
        circuits = []
        for size in range(1, min(len(zero), 5) + 1):
            for J in itertools.combinations(zero, size):
                if any(set(C) <= set(J) for C in circuits): continue
                rk = rank(lonely_rows(J))
                if rk < sum(rho[p] for p in J):
                    circuits.append(J)
                    # binary pure tensors in R not in Y: R/Y(x)F^2 = span of lonely rows
                    Rb, pb = rref(lonely_rows(J), 2 * L * k)
                    extra = []
                    for p in range(n):
                        for th in (1, 2, 3):
                            e = reduce_mod(Y, piv, tensor(th, G[p], L))
                            if not any(e): continue
                            if in_span(Rb, pb, e + [0] * len(e)) and in_span(Rb, pb, [0] * len(e) + e): extra.append((p, th))
                    dsum = rank([vec for p in J for vec in red[p]])
                    sig = (tuple(sorted(rho[p] for p in J)), dsum, sum(rho[p] for p in J) - rk, len(extra) > 0)
                    stats[sig] += 1
                    if verbose or not extra:
                        print('Q =', ' '.join(Q), '| dim V/Y', dimV, '| J', J, 'rho', [rho[p] for p in J], 'dim sum', dsum, 'defect', sum(rho[p] for p in J) - rk, 'binary tensors in R outside Y:', extra)
    print('signatures (rho of the circuit, dim of the sum of planes, defect, some binary tensor outside Y in R): count')
    for sig, c in sorted(stats.items()): print(' ', sig, c)

main()
