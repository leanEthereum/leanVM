"""Note 86: the solution of a pattern with a one-dimensional kernel: are the three members distinct, and where do they agree?
usage: 86_list.py v r patterns.txt [seed]"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import importlib; lib = importlib.import_module('86_lib')
L = 2
def main():
    v, r, fn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    T = lib.Tree(v, r, seed); G = T.rows(0); k = T.k
    for line in open(fn):
        P = line.split('|')[0].split()
        if len(P) != T.n: continue
        ker = lib.kernel(lib.pattern_rows(G, P, L), L * k)
        print('w', lib.weight(P), 'kernel dimension', len(ker))
        if len(ker) != 1: continue
        M = ker[0]; d1, d2 = M[:k], M[k:]
        c1 = [lib.dot(d1, g) for g in G]; c2 = [lib.dot(d2, g) for g in G]
        z1 = sum(1 for a in c1 if a == 0); z2 = sum(1 for a in c2 if a == 0); z3 = sum(1 for a, b in zip(c1, c2) if a == b)
        print('  d1, d2, d1+d2 nonzero:', any(d1), any(d2), d1 != d2, '| zeros of d1, d2, d1+d2 on the', T.n, 'leaves:', z1, z2, z3)
        ag = [0, 0, 0]
        for x in range(T.n):  # agreement with the majority word: member l agrees where it is in a class of size >= 2 of equal values
            vals = [0, c1[x], c2[x]]
            for l in range(3):
                if sum(1 for u in vals if u == vals[l]) >= 2: ag[l] += 1
        print('  agreement of the three members with the plurality word:', ag)
main()
