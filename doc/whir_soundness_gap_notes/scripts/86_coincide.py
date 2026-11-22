"""Note 86, experiment B: coincidences of non-binary lines. For a three-member pattern Q on the code (2^v, 2^(v+r)) and two zero
nodes p, q of Q: is the intersection of the planes K^2 (x) g_p and K^2 (x) g_q modulo Y = R(Q) a line that is not binary on either side,
and does Y + line contain a binary pure tensor theta (x) g_s outside Y?
usage: 86_coincide.py v r (all | count) seed"""
import sys, random, itertools, collections
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
mul, rref, rank, reduce_mod, tensor, in_span, kernel = lib.mul, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.in_span, lib.kernel
def isbin(a, b): return a == 0 or b == 0 or a == b
def main():
    v, r, mode, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    T = lib.Tree(v, r, seed); G = T.rows(0); n = T.n; k = T.k; L = 2
    rnd = random.Random(seed * 7919 + 1)
    toks = ['.', '01', '02', '12', '012']
    if mode == 'all': gen = itertools.product(toks, repeat=n)
    else:
        def g():
            for _ in range(int(mode)):
                dens = rnd.choice([0.3, 0.5, 0.7]); yield tuple(rnd.choice(toks[1:]) if rnd.random() < dens else '.' for _ in range(n))
        gen = g()
    stats = collections.Counter(); shown = 0
    for Q in gen:
        zero = [p for p in range(n) if Q[p] == '.']
        if len(zero) < 2: continue
        Y, piv = rref(lib.pattern_rows(G, Q, L), L * k) if lib.weight(Q) else ([], [])
        if L * k - len(piv) < 2: continue
        red = {p: [reduce_mod(Y, piv, tensor(th, G[p], L)) for th in (1, 2)] for p in zero}
        for p, q in itertools.combinations(zero, 2):
            ker = kernel([list(c) for c in zip(*(red[p] + red[q]))], 4)  # a1 e1gp + a2 e2gp + b1 e1gq + b2 e2gq = 0 mod Y
            # remove the parts where the p-side or the q-side alone vanishes mod Y
            if len(ker) != 1: stats[('dim', len(ker))] += 1; continue
            a1, a2, b1, b2 = ker[0]
            if (a1 == 0 and a2 == 0) or (b1 == 0 and b2 == 0): stats['one-sided'] += 1; continue
            kind = ('bin' if isbin(a1, a2) else 'NON', 'bin' if isbin(b1, b2) else 'NON')
            lam = [mul(a1, x) ^ mul(a2, y) for x, y in zip(red[p][0], red[p][1])]
            Y2, piv2 = rref(Y + [lam], L * k)
            extra = [(s, th) for s in range(n) for th in (1, 2, 3) if not in_span(Y, piv, tensor(th, G[s], L)) and in_span(Y2, piv2, tensor(th, G[s], L))]
            stats[(kind, 'binary tensor in Y+line' if extra else 'NO BINARY TENSOR')] += 1
            if kind == ('NON', 'NON') and shown < 30:
                shown += 1; print(' '.join(Q), '| nodes', p, q, '| dim V/Y', L * k - len(piv), '| binary tensors in Y + line outside Y:', extra)
    for s, c in sorted(stats.items(), key=str): print(' ', s, c)
main()
