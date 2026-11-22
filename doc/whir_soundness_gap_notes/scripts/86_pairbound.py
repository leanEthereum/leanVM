"""Note 86: on the patterns that violate (C*), check that the rank is B(P; R(Qa) cap R(Qb)) for two BINARY patterns Qa, Qb one level up:
Qa = Q* with triples at the pairs of the lonely triples carrying a non-binary line in one level-2 block, Qb the same for the other block.
usage: 86_pairbound.py v r patterns.txt [seed]"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib'); hull = None
mul, inv, rref, rank, reduce_mod, tensor, in_span, kernel = lib.mul, lib.inv, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.in_span, lib.kernel
L = 2
def up_vec(vec, b):
    K = len(vec) // 2; out = [0] * (4 * K)
    for a in range(2):
        for e in range(K): out[a * 2 * K + 2 * e + b] = vec[a * K + e]
    return out
def intersect(A, B, ncols):
    """basis of rowspace(A) cap rowspace(B)"""
    if not A or not B: return []
    ker = kernel([list(c) for c in zip(*(A + B))], len(A) + len(B))
    out = []
    for kv in ker:
        vec = [0] * ncols
        for c, u in zip(kv[:len(A)], A):
            if c: vec = [x ^ mul(c, y) for x, y in zip(vec, u)]
        out.append(vec)
    return rref(out, ncols)[0] if out else []
def main():
    v, r, fn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    T = lib.Tree(v, r, seed); G0, G1 = T.rows(0), T.rows(1); k = T.k; n1 = T.n // 2
    tot = ok = 0
    for line in open(fn):
        P = line.split('|')[0].split()
        if len(P) != T.n: continue
        R, piv = rref(lib.pattern_rows(G0, P, L), L * k); rk = len(piv)
        inR = lambda u: in_span(R, piv, up_vec(u, 0)) and in_span(R, piv, up_vec(u, 1))
        Qs = []
        for p in range(n1):
            s = tuple(th for th in (1, 2, 3) if inR(tensor(th, G1[p], L)))
            Qs.append({(): '.', (1,): '01', (2,): '02', (3,): '12', (1, 2, 3): '012'}[s])
        lon = []
        for x, tok in enumerate(P):
            p = x >> 1
            if tok != '012' or Qs[p] == '012': continue
            e1, e2 = tensor(1, G1[p], L), tensor(2, G1[p], L); cond = []
            for b in (0, 1):
                r1, r2 = reduce_mod(R, piv, up_vec(e1, b)), reduce_mod(R, piv, up_vec(e2, b)); cond += [[a, c] for a, c in zip(r1, r2)]
            ker = kernel(cond, 2)
            if len(ker) == 1 and not (ker[0][0] == 0 or ker[0][1] == 0 or ker[0][0] == ker[0][1]): lon.append(p)
        blocks = sorted(set(p >> 1 for p in lon))
        if len(blocks) != 2: print('unexpected shape: lonely pairs', lon); tot += 1; continue
        Qa = [('012' if (p in lon and p >> 1 == blocks[0]) else Qs[p]) for p in range(n1)]
        Qb = [('012' if (p in lon and p >> 1 == blocks[1]) else Qs[p]) for p in range(n1)]
        Ra = rref(lib.pattern_rows(G1, Qa, L), L * k // 2)[0]; Rb = rref(lib.pattern_rows(G1, Qb, L), L * k // 2)[0]
        Y = intersect(Ra, Rb, L * k // 2); Yr, Yp = rref(Y, L * k // 2)
        Bv = 2 * len(Yp) + sum(rank([reduce_mod(Yr, Yp, tensor(th, G1[x >> 1], L)) for th in lib.basis_of(tok)]) for x, tok in enumerate(P) if tok != '.')
        rQ = rank(lib.pattern_rows(G1, Qs, L)); Qab = [('012' if p in lon else Qs[p]) for p in range(n1)]
        tot += 1; ok += Bv == rk
        print('rank', rk, '| r(Q*)', rQ, 'r(Qa)', len(Ra), 'r(Qb)', len(Rb), 'r(Qa v Qb)', rank(lib.pattern_rows(G1, Qab, L)), 'dim R(Qa) cap R(Qb)', len(Yp), '| B(P; R(Qa) cap R(Qb)) =', Bv, '' if Bv == rk else ' <-- not exact')
    print('patterns', tot, '; rank = B(P; R(Qa) cap R(Qb)) on', ok)
main()
