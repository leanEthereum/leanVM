"""Note 38, Theorem 3.1 (low rates): exact count at rate 1/4, N = 6, c = 2 against the lower bound.
All A of 16 points that are disjoint unions of affine flats of size >= 8 and avoid the subspace P of 4 points."""
import itertools, importlib, sys
sys.path.insert(0, sys.path[0])
Lc = importlib.import_module("38_lists_check")
N, n = 6, 64
par = lambda v: bin(v).count("1") & 1
P = sum(1 << x for x in range(4))                      # span(1, x): codimension 4


def flats(codim):
    out = set()
    for fs in itertools.combinations(range(1, n), codim):
        # independent functionals
        span = {0}
        ok = True
        for f in fs:
            if f in span:
                ok = False
                break
            span |= {s ^ f for s in span}
        if not ok:
            continue
        for cs in itertools.product((0, 1), repeat=codim):
            out.add(sum(1 << x for x in range(n) if all(par(f & x) == c for f, c in zip(fs, cs))))
    return out


f3 = [f for f in flats(3) if f & P == 0]
f2 = [f for f in flats(2) if f & P == 0]
A = set(f2)
for i, a in enumerate(f3):
    for b in f3[i + 1:]:
        if a & b == 0:
            A.add(a | b)
bound = (2**4 - 1) * (Lc.Q2_formula(5) - 2**6 + 2)
print(f"rate 1/4, N=6, c=2 (agreement 20/64 = 5n/16, degree <= 16): flats of 8 points avoiding P: {len(f3)}, of 16 points: {len(f2)}")
print(f"exact number of sets A: {len(A)}   lower bound of Theorem 3.1: {bound}   {'OK' if len(A) >= bound else 'VIOLATED'}")
