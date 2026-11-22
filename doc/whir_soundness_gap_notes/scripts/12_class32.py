# Researcher 12. Classes in the formal model at n = 32, modulus 4 on n_phi (depths 2 and 3), from a seed:
# the class of S0 is contained in S0 + RM(2,5) (note 12, Lemma 1.2). Prints the class size and, for every nonzero h,
# how many members are invariant under translation by h. Used in Theorem 5.2 of note 12:
# the class of cff3c000 (seven cosets of the line {0,1}) has 2395 members, 715 of them invariant under h = 1.
# usage: python3 12_class32.py [hexseed ...]
import sys
N = 5; n = 32
H = [sum(1 << x for x in range(n) if bin(p & x).count('1') & 1) for p in range(n)]
basis = [(1 << n) - 1] + [H[1 << i] for i in range(N)] + [H[1 << i] & H[1 << j] for i in range(N) for j in range(i + 1, N)]
def cls(s0, mod=4):
    t = bin(s0).count('1'); r = [bin(s0 & H[p]).count('1') % mod for p in range(n)]
    out = []
    for g in range(1 << len(basis)):
        q = 0
        for i in range(len(basis)):
            if g >> i & 1: q ^= basis[i]
        s = s0 ^ q
        if bin(s).count('1') != t: continue
        if all(bin(s & H[p]).count('1') % mod == r[p] for p in range(1, n)): out.append(s)
    return out
def inv(s, h): return all(((s >> x) & 1) == ((s >> (x ^ h)) & 1) for x in range(n))
seeds = [int(a, 16) for a in sys.argv[1:]] or [0xcff3c000, 0x58851331]
for seed in seeds:
    C = cls(seed)
    print(hex(seed), "size", bin(seed).count('1'), "class", len(C), "invariant members per h:", [(h, c) for h in range(1, n) for c in [sum(inv(s, h) for s in C)] if c])
