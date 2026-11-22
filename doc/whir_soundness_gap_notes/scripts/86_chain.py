"""Note 86: the chain of rational full parts Y_0 = R(P), Y_1, Y_2, ... of a pattern and the one-level identity at every level.
Y_{h+1} is spanned by the nu (x) g_u (u a node of level h+1, nu in K^L) with nu (x) g_u (x) F^2 inside Y_h for three draws of the twiddles
of level h (so nu does not move with them). Identity at level h:  dim Y_h = 2 dim Y_{h+1} + sum_u dim (Xi_u (x) g_parent(u) + Y_{h+1}) / Y_{h+1},
Xi_u the space of the node u in Y_h. Prints the defect (right side minus left side) at every level, and the same with the binary part only.
usage: 86_chain.py m v r patterns.txt [seed]"""
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
def redraw(T, h, rnd):
    T2 = copy.deepcopy(T); T2.tw[h] = [lib.rnd_elt(rnd) for _ in T2.tw[h]]; return T2
def chain(T, P, L, h, rnd):
    """returns Xi: list over the nodes of level h of bases (lists of field vectors of length L) of the node spaces of Y_h"""
    if h == 0: return [[[(th >> a) & 1 for a in range(L)] for th in lib.basis_of(tok)] for tok in P]
    draws = [T, redraw(T, h - 1, rnd), redraw(T, h - 1, rnd)]
    G = T.rows(h); K = T.dim(h); conds = [[] for _ in G]
    for Tj in draws:
        Xj = chain(Tj, P, L, h - 1, rnd); Gl = Tj.rows(h - 1)
        rows = [tensor_K(nu, Gl[x]) for x in range(len(Gl)) for nu in Xj[x]]
        R, piv = rref(rows, 2 * L * K) if rows else ([], [])
        for u in range(len(G)):
            for b in (0, 1):
                reds = [reduce_mod(R, piv, up_vec(tensor_K(unit(a, L), G[u]), b, L)) for a in range(L)]
                conds[u] += [[reds[a][c] for a in range(L)] for c in range(2 * L * K)]
    return [kernel(conds[u], L) for u in range(len(G))]
def is_binary_space(bas, L):
    """dimension of the F_2-rational part of the span of bas"""
    if not bas: return 0
    R, piv = rref(bas, L); cnt = 0; span = {0}
    for th in range(1, 1 << L):
        if th in span: continue
        if in_span(R, piv, [(th >> a) & 1 for a in range(L)]): cnt += 1; span |= {s ^ th for s in span}
    return cnt
def main():
    m, v, r, fn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]; seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    L = m - 1; T = lib.Tree(v, r, seed)
    for line in open(fn):
        P = line.split('|')[0].split()
        if len(P) != T.n: continue
        print('pattern:', ' '.join(P))
        rnd = random.Random(seed + 77)
        Xs = [chain(T, P, L, h, random.Random(seed + 77)) for h in range(v + 1)]
        dims = []
        for h in range(v + 1):
            G = T.rows(h); rows = [tensor_K(nu, G[u]) for u in range(len(G)) for nu in Xs[h][u]]
            dims.append(rank(rows) if rows else 0)
        for h in range(v):
            Gu = T.rows(h + 1); rows = [tensor_K(nu, Gu[u]) for u in range(len(Gu)) for nu in Xs[h + 1][u]]
            Yr, Yp = rref(rows, L * T.dim(h + 1)) if rows else ([], [])
            s = 2 * len(Yp)
            for u in range(T.nodes(h)):
                if Xs[h][u]: s += rank([reduce_mod(Yr, Yp, tensor_K(nu, Gu[u >> 1])) for nu in Xs[h][u]])
            nonbin = sum(len(Xs[h + 1][u]) - is_binary_space(Xs[h + 1][u], L) for u in range(len(Gu)))
            print('  level %d: dim Y_%d = %d, weight of its node spaces %d; dim Y_%d = %d, of which not binary %d; identity gives %d, defect %d' % (h, h, dims[h], sum(len(x) for x in Xs[h]), h + 1, dims[h + 1], nonbin, s, s - dims[h]))
main()
