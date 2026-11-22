"""Note 38: writes toy list families as bitmasks for 38_collide.c. Usage: 38_families.py NAME > file
  flats    rate 1/4, N = 5: the 62 affine hyperplanes (word X^16, degree <= 8)
  five8    rate 1/2, N = 5: the 1400 members of the 5n/8 class (note 05, Theorem 2.1)
  nested   rate 1/2, N = 5: the 36540 members of the nested family of note 38 at agreement 18 = 9n/16
  pigeon   rate 1/2, N = 4: all 10-subsets of D with element sum 0 (the class of e_1 = 0; degree <= 8)"""
import sys, itertools, importlib
sys.path.insert(0, sys.path[0])
par = lambda v: bin(v).count("1") & 1
name = sys.argv[1]
if name == "flats":
    N = 5
    out = [sum(1 << x for x in range(32) if par(a & x) == c) for a in range(1, 32) for c in (0, 1)]
elif name == "five8":
    N = 5
    W = [0, 1, 2, 3]                                   # codimension 3, cosets indexed by x >> 2
    coset = lambda i: sum(1 << x for x in range(32) if x >> 2 == i)
    out = set()
    for five in itertools.combinations(range(8), 5):
        out.add(sum(coset(i) for i in five))
    for h in range(1, 8):                              # hyperplane H = {par((h<<2) & x) = 0} contains W
        H = [x for x in range(32) if par((h << 2) & x) == 0]
        for a in range(1, 32):                         # V = H cap ker a, must not contain W: a restricted to W nonzero
            if a & 3 == 0:
                continue
            for cH in (0, 1):
                for ca in (0, 1):
                    F = sum(1 << x for x in range(32) if par((h << 2) & x) == cH and par(a & x) == ca)
                    other = [i for i in range(8) if par(h & i) != cH]
                    for three in itertools.combinations(other, 3):
                        out.add(F | sum(coset(i) for i in three))
    out = sorted(out)
    assert len(out) == 1400 and all(bin(s).count("1") == 20 for s in out)
elif name == "nested":
    N = 5
    L = importlib.import_module("38_lists_check")
    q2 = L.all_Q2(L.cube(N, 16, 16), 15)
    q1 = L.all_Q1(L.cube(N, 24, 8), 7)
    X00 = L.cube(N, 24, 0)
    last = [sum(1 << x for x in X00 if par(a & x) == 1) for a in (4, 2, 6)]
    P = sum(1 << x for x in L.cube(N, 30, 0))
    out = sorted({a | b | c | P for a in q2 for b in q1 for c in last})
elif name == "pigeon":
    N = 4
    out = []
    for c in itertools.combinations(range(16), 10):
        s = 0
        for x in c:
            s ^= x
        if s == 0:
            out.append(sum(1 << x for x in c))
print(N)
for s in out:
    print(f"{s:x}")
