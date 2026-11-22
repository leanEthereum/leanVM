# Note 79, Theorem 6.2: the threshold tau solving 64((L+1) tau - 1 - L rho) = (L+1) H(tau) + log2 C, and the level-0 query count 108 / log2(1/tau).
from math import log2, ceil
def H(t): return -t*log2(t) - (1-t)*log2(1-t)
def tau(L, rho, C):
    t = (1 + L*rho)/(L+1)
    for _ in range(200): t = (1 + L*rho)/(L+1) + H(t)/64 + log2(C)/(64*(L+1))
    return t
for rho in (0.5, 0.25):
    for C in (1, 2.62, 4):
        print("rho", rho, "C", C, " ".join("L=%d: %.4f (%d q)" % (L, tau(L, rho, C), ceil(108/log2(1/tau(L, rho, C)))) for L in (1, 2, 3, 4, 8, 16)))
    print("  Johnson", rho**0.5, ceil(108/log2(1/rho**0.5)))
