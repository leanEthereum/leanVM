"""Note 86: the one-level identity with the rational full part on given three-member patterns.
For each pattern: rank, B(P;Q*) (binary full part), and B(P;Y^K) with Y^K = Y* + the lines nu (x) g_p of the full parts of triple
leaves that do not move when the bottom twiddles are redrawn (rational over K_1; not binary).
usage: 86_hull.py v r patterns.txt [seed]     (one pattern per line, leaves separated by spaces; text after '|' is ignored)"""
import sys, random, copy
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
mul, inv, rref, rank, reduce_mod, tensor, tensor_K, in_span, kernel = lib.mul, lib.inv, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.tensor_K, lib.in_span, lib.kernel
L = 2
def up_vec(vec, b):  # u in V_1 -> u (x) e_b in V_0 (bottom index is the low bit)
    K = len(vec) // 2; out = [0] * (4 * K)
    for a in range(2):
        for e in range(K): out[a * 2 * K + 2 * e + b] = vec[a * K + e]
    return out
def analyse(T, P):
    G0, G1 = T.rows(0), T.rows(1); k = T.k
    R, piv = rref(lib.pattern_rows(G0, P, L), L * k)
    inR = lambda u: in_span(R, piv, up_vec(u, 0)) and in_span(R, piv, up_vec(u, 1))
    Qs = {p: [th for th in (1, 2, 3) if inR(tensor(th, G1[p], L))] for p in range(T.n // 2)}
    lines = {}
    for x, tok in enumerate(P):
        if tok != '012': continue
        p = x >> 1
        if len(Qs[p]) == 3: continue
        e1, e2 = tensor(1, G1[p], L), tensor(2, G1[p], L)
        cond = []
        for b in (0, 1):
            r1, r2 = reduce_mod(R, piv, up_vec(e1, b)), reduce_mod(R, piv, up_vec(e2, b))
            cond += [[a, c] for a, c in zip(r1, r2)]
        ker = kernel(cond, 2)
        if len(ker) == 1:
            a, c = ker[0]
            if a == 0 or c == 0 or a == c: continue  # binary: already in Q*
            lines[x] = mul(a, inv(c)) if c else None  # projective coordinate a/c
    return len(piv), Qs, lines, G1
def main():
    v, r, fn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    T = lib.Tree(v, r, seed); T2 = copy.deepcopy(T); rnd = random.Random(seed + 1000)
    T2.tw[0] = [lib.rnd_elt(rnd) for _ in T2.tw[0]]
    tot = fail_star = fail_hull = 0
    for line in open(fn):
        P = line.split('|')[0].split()
        if len(P) != T.n: continue
        rk, Qs, lines, G1 = analyse(T, P); rk2, Qs2, lines2, _ = analyse(T2, P)
        rat = {x: c for x, c in lines.items() if lines2.get(x) == c}; irr = len(lines) - len(rat)
        def Bof(extra):
            Y = [tensor(th, G1[p], L) for p in Qs for th in Qs[p]] + extra
            Yr, Yp = rref(Y, L * T.k // 2) if Y else ([], [])
            s = 2 * len(Yp)
            for x, tok in enumerate(P):
                s += rank([reduce_mod(Yr, Yp, tensor(th, G1[x >> 1], L)) for th in lib.basis_of(tok)]) if tok != '.' else 0
            return s
        Bstar = Bof([]); BK = Bof([tensor_K([c, 1], G1[x >> 1]) for x, c in rat.items()])
        tot += 1; fail_star += Bstar != rk; fail_hull += BK != rk
        print('w', lib.weight(P), 'rank', rk, 'B(P;Q*)', Bstar, 'B(P;Y^K)', BK, '| rational non-binary lines at leaves', sorted(rat), '| moving lines:', irr, '' if BK == rk else '  <-- HULL IDENTITY FAILS')
    print('patterns', tot, '; (C*) fails on', fail_star, '; identity with the rational full part fails on', fail_hull)
main()
