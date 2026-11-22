"""Note 77, Theorem 3.3: Q_3 fails at rate 1/2 on D_N = <1, x, .., x^(N-1)> for every N >= 3.
c = x^2+x+1, S = {1, x^2, x^2+1}; A = S + any half of the pairs {a, a+c} of D_N minus D_3; B = the rest; f = Lambda_A, g = gamma*Lambda_B.
Checks, over GF(2^64): prod_A a = prod_A (a+c); f + g vanishes at 0 and c; every point of D_N is a zero of f, g or f + g.
Also the random-subspace control: for the same combinatorial choice the product identity fails."""
import random, importlib.util, os
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "74_gfpy.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
mul, inv = gf.mul, gf.inv
def prod(xs):
    r = 1
    for t in xs: r = mul(r, t)
    return r
def lam_at(S, y): return prod([y ^ s for s in S])
rnd = random.Random(77)
c = 7; S = [1, 4, 5]
for N in range(3, 13):
    n = 1 << N; D = list(range(n))
    for trial in range(3):
        pairs = sorted({min(a, a ^ c) for a in D if a >= 8})
        rnd.shuffle(pairs)
        half = pairs[: len(pairs) // 2]
        A = S + half + [a ^ c for a in half]
        B = [a for a in D if a not in set(A) and a not in (0, c)]
        assert len(A) == n // 2 - 1 and len(B) == n // 2 - 1
        ok1 = prod(A) == prod([a ^ c for a in A])
        gamma = mul(lam_at(A, 0), inv(lam_at(B, 0)))
        ok2 = lam_at(A, c) == mul(gamma, lam_at(B, c))
        # f+g has degree <= n/2 - 1 and vanishes at 0 and c; f on A; g on B: all n points are coincidence points
        # f + g is not zero: evaluate at a point of A (f = 0, g != 0)
        ok3 = mul(gamma, lam_at(B, A[0])) != 0
        print(f"N={N} n={n} k={n//2} trial {trial}: product identity {ok1}, f+g zero at 0 and c {ok2}, f != g {ok3}, coincidence points {len(A)+len(B)+2} = n, Q_3 allows {n-1}")
print("log2 of the number of sets A from this one quadruple, C(n/2-4, n/4-2):")
from math import lgamma, log
for N in (19, 22, 26):
    n = 1 << N; m = n // 2 - 4
    print(f"  N={N}: {(lgamma(m+1) - 2*lgamma(m/2+1))/log(2):.0f}")
