"""Note 86, experiment A2: as 86_lonely.py, but keeps only the circuits J of the lonely system in which some node of J
has a full part (vectors u of U_p mod Y with u (x) F^2 inside R mod Y) that is a line not spanned by a binary theta (x) g_p.
usage: 86_lonely2.py v r count seed [maxsize]"""
import sys, random, itertools, collections
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
mul, rref, rank, reduce_mod, tensor, in_span, kernel = lib.mul, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.in_span, lib.kernel

def full_part(Rb, pb, vecs):
    """subspace of span(vecs) of u with u(x)(1,0) and u(x)(0,1) in the row space (Rb,pb); returns coefficient vectors"""
    m = len(vecs); n = len(vecs[0])
    # unknown c in K^m: sum c_i vecs_i (x) e_b reduced mod Rb must vanish: linear conditions
    cond = []
    for b in (0, 1):
        reds = [reduce_mod(Rb, pb, (v + [0] * n) if b == 0 else ([0] * n + v)) for v in vecs]
        for col in range(2 * n): cond.append([reds[i][col] for i in range(m)])
    return kernel(cond, m)

def main():
    v, r, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    maxsize = int(sys.argv[5]) if len(sys.argv) > 5 else 5
    T = lib.Tree(v, r, seed); G = T.rows(0); n = T.n; k = T.k; L = 2
    rnd = random.Random(seed * 7919 + 1)
    toks = ['.', '01', '02', '12', '012']
    stats = collections.Counter(); shown = 0
    for it in range(count):
        dens = rnd.choice([0.3, 0.5, 0.7])
        Q = [rnd.choice(toks[1:]) if rnd.random() < dens else '.' for _ in range(n)]
        Y, piv = rref(lib.pattern_rows(G, Q, L), L * k) if lib.weight(Q) else ([], [])
        if L * k - len(piv) == 0: continue
        zero = [p for p in range(n) if Q[p] == '.']
        red = {p: [reduce_mod(Y, piv, tensor(th, G[p], L)) for th in (1, 2)] for p in zero}
        rho = {p: rank(red[p]) for p in zero}
        zs = {p: (lib.rnd_elt(rnd), lib.rnd_elt(rnd)) for p in range(n)}
        def lonely_rows(J):
            return [[mul(c, zs[p][0]) if c else 0 for c in vec] + [mul(c, zs[p][1]) if c else 0 for c in vec] for p in J for vec in red[p]]
        circuits = []
        for size in range(1, min(len(zero), maxsize) + 1):
            for J in itertools.combinations(zero, size):
                if any(set(C) <= set(J) for C in circuits): continue
                rk = rank(lonely_rows(J))
                if rk >= sum(rho[p] for p in J): continue
                circuits.append(J)
                Rb, pb = rref(lonely_rows(J), 2 * L * k)
                kinds = []
                for p in J:
                    fp = full_part(Rb, pb, red[p])
                    # kernel of the map K^2 -> U_p mod Y adds to fp when rho < 2; classify the line(s)
                    if len(fp) == 2: kinds.append('all')
                    elif len(fp) == 0: kinds.append('0')
                    else:
                        a, b = fp[0]
                        binary = (a == 0) or (b == 0) or (a == b)
                        kinds.append('bin' if binary else 'NONBIN')
                sig = (tuple(sorted(rho[p] for p in J)), tuple(sorted(kinds)))
                stats[sig] += 1
                if 'NONBIN' in kinds and shown < 40:
                    shown += 1
                    extra = []
                    for p in range(n):
                        for th in (1, 2, 3):
                            e = reduce_mod(Y, piv, tensor(th, G[p], L))
                            if any(e) and in_span(Rb, pb, e + [0] * len(e)) and in_span(Rb, pb, [0] * len(e) + e): extra.append((p, th))
                    print('Q =', ' '.join(Q), '| dim V/Y', L * k - len(piv), '| J', J, 'rho', [rho[p] for p in J], 'full parts', kinds, 'defect', sum(rho[p] for p in J) - rk, 'binary in R outside Y:', extra)
    print('signatures (rho of the circuit, kinds of full parts): count')
    for sig, c in sorted(stats.items()): print(' ', sig, c)
main()
