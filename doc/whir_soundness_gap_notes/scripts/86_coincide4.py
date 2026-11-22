"""Note 86: search for non-binary coincidences with m members on the code (2^v, 2^(v+r)) (class patterns Q2, class extensions at two nodes).
For Q2 and nodes a != b with classes Ca > Q2[a], Cb > Q2[b]: I = (Lambda_a (x) g_a + Y) cap (Lambda_b (x) g_b + Y) mod Y, Y = R(Q2).
Reports the cases where Y + I is not spanned, modulo Y, by binary pure tensors theta (x) g_s, and writes the lifted patterns
(blocks of four leaves: three leaves Ca + one Q2[a]; two leaves Cb + two Q2[b]; other blocks Q2 quadrupled) to stdout prefixed by 'P: '.
usage: 86_coincide4.py m v r (all | count) seed"""
import sys, random, itertools, collections
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
mul, rref, rank, reduce_mod, tensor, in_span, kernel = lib.mul, lib.rref, lib.rank, lib.reduce_mod, lib.tensor, lib.in_span, lib.kernel
def main():
    m, v, r, mode, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5])
    L = m - 1
    T = lib.Tree(v, r, seed); G = T.rows(0); n = T.n; k = T.k
    rnd = random.Random(seed * 7919 + 1)
    classes = ['.'] + [''.join(map(str, c)) for s in range(2, m + 1) for c in itertools.combinations(range(m), s)]
    sup = {c: [d for d in classes if d != c and (c == '.' or set(c) < set(d))] for c in classes}
    if mode == 'all': gen = itertools.product(classes, repeat=n)
    else: gen = (tuple(rnd.choice(classes) if rnd.random() < 0.6 else '.' for _ in range(n)) for _ in range(int(mode)))
    found = 0; tested = 0
    for Q in gen:
        Y, piv = rref(lib.pattern_rows(G, Q, L), L * k) if lib.weight(Q) else ([], [])
        if L * k - len(piv) < 2: continue
        binred = [(s, th, reduce_mod(Y, piv, tensor(th, G[s], L))) for s in range(n) for th in range(1, 1 << L)]
        for a, b in itertools.combinations(range(n), 2):
            for Ca in sup[Q[a]]:
                Ua = [reduce_mod(Y, piv, tensor(th, G[a], L)) for th in lib.basis_of(Ca)]; Ua = rref(Ua, L * k)[0]
                if not Ua: continue
                for Cb in sup[Q[b]]:
                    Ub = [reduce_mod(Y, piv, tensor(th, G[b], L)) for th in lib.basis_of(Cb)]; Ub = rref(Ub, L * k)[0]
                    if not Ub: continue
                    tested += 1
                    ker = kernel([list(c) for c in zip(*(Ua + Ub))], len(Ua) + len(Ub))
                    if not ker: continue
                    I = [[0] * (L * k) for _ in ker]
                    for j, kv in enumerate(ker):
                        for c, u in zip(kv[:len(Ua)], Ua):
                            if c: I[j] = [x ^ mul(c, y) for x, y in zip(I[j], u)]
                    Ir, Ip = rref(I, L * k)
                    binI = [e for (s, th, e) in binred if any(e) and in_span(Ir, Ip, e)]
                    if rank(binI) < len(Ip):
                        found += 1
                        if found <= 60:
                            P = []
                            for s in range(n):
                                if s == a: P += [Ca, Ca, Q[s], Ca]
                                elif s == b: P += [Q[s], Cb, Q[s], Cb]
                                else: P += [Q[s]] * 4
                            print('Q2 =', ' '.join(Q), '| nodes', a, b, 'classes', Ca, Cb, '| dim I', len(Ip), 'binary part', rank(binI))
                            print('P:', ' '.join(P))
    print('tested', tested, 'non-binary coincidences', found)
main()
