#!/usr/bin/env python3
"""Note 62, section 2: expansion of the random d-out window graph.

Model: for every x the partner set is a uniform d-subset of D minus {x}, independently.
For a fixed Z of size z, each x in Z has W_x inside Z with probability
p_z = C(z-1,d)/C(n-1,d), independently, so |int Z| is Binomial(z, p_z).
First moment over all Z with |Z| <= phi0*n:
  fail(gamma, a0) <= sum_z C(n,z) * Pr[Bin(z,p_z) >= floor(gamma*z + a0) + 1].
The sum is bounded block by block (z in [z1,z2], ratio 1+2^-7): C(n,z) by its maximum on
the block, the tail by Pr[Bin(z2,p_{z2}) >= floor(gamma*z1 + a0) + 1] (monotone in z and p),
the tail by min(Chernoff, union over g-subsets). All bounds are upper bounds, so the
gamma printed is valid (slightly conservative). Usage: python3 62_expansion.py [quick]
"""
import math, sys

LG = math.lgamma
LN2 = math.log(2.0)


def lbinom(n, k):
    if k < 0 or k > n:
        return -math.inf
    return (LG(n + 1) - LG(k + 1) - LG(n - k + 1)) / LN2


def log2_p(n, z, d):
    if z - 1 < d:
        return -math.inf
    s = 0.0
    for i in range(d):
        s += math.log((z - 1 - i) / (n - 1 - i))
    return s / LN2


def log2_tail(m, lp, g):
    """log2 of an upper bound for Pr[Bin(m, 2^lp) >= g]."""
    if g <= 0:
        return 0.0
    if g > m or lp == -math.inf:
        return -math.inf
    best = lbinom(m, g) + g * lp  # union over g-subsets
    p = 2.0 ** lp
    a = g / m
    if a > p and p < 1.0:
        if a >= 1.0:
            dkl = -math.log(p)
        else:
            dkl = a * math.log(a / p) + (1 - a) * math.log((1 - a) / (1 - p))
        best = min(best, -m * dkl / LN2)
    return min(best, 0.0)


def log2_fail(n, d, phi0, gamma, a0, ratio=1.0 + 2.0 ** -7):
    zmax = int(phi0 * n)
    terms = []
    z1 = d + 1
    while z1 <= zmax:
        z2 = min(zmax, max(z1, int(z1 * ratio)))
        # max of C(n,z) on the block
        if z2 <= n // 2:
            lb = lbinom(n, z2)
        elif z1 >= n // 2:
            lb = lbinom(n, z1)
        else:
            lb = lbinom(n, n // 2)
        g = int(math.floor(gamma * z1 + a0)) + 1
        t = lb + log2_tail(z2, log2_p(n, z2, d), g) + math.log2(z2 - z1 + 1)
        terms.append(t)
        z1 = z2 + 1
    mx = max(terms)
    if mx == -math.inf:
        return -math.inf
    return mx + math.log2(sum(2.0 ** (t - mx) for t in terms if t > mx - 200))


def gamma_min(n, d, phi0, a0, target=-129.0):
    lo, hi = 0.0, 1.0
    if log2_fail(n, d, phi0, hi, a0) > target:
        return None
    for _ in range(11):
        mid = (lo + hi) / 2
        if log2_fail(n, d, phi0, mid, a0) <= target:
            hi = mid
        else:
            lo = mid
    return hi


def gamma_asym(d, phi):
    """root of D(gamma || phi^d) = H(phi)/phi (bits): the n -> infinity value."""
    p = phi ** d
    H = -(phi * math.log2(phi) + (1 - phi) * math.log2(1 - phi)) if 0 < phi < 1 else 0.0
    rhs = H / phi
    lo, hi = p, 1.0 - 1e-12
    for _ in range(80):
        mid = (lo + hi) / 2
        dk = mid * math.log2(mid / p) + (1 - mid) * math.log2((1 - mid) / (1 - p))
        if dk >= rhs:
            hi = mid
        else:
            lo = mid
    return hi


def delta_w3(n, d, target=-129.0):
    """least j with n * C(n-1,j) (d/(n-1))^j <= 2^target: in-degree < j, so Delta = j."""
    j = d
    while True:
        j += 1
        if math.log2(n) + lbinom(n - 1, j) + j * math.log2(d / (n - 1)) <= target:
            return j


def main():
    quick = len(sys.argv) > 1 and sys.argv[1] == "quick"
    Ns = [10, 25] if quick else [10, 16, 20, 25, 28]
    ds = [6, 8] if quick else [4, 6, 8, 10, 12]
    phis = [1 / 16, 1 / 8, 1 / 4, 1 / 2, 3 / 4]
    print("asymptotic gamma(d, phi): root of D(gamma || phi^d) = H(phi)/phi")
    print("d    " + "  ".join("phi=%-6.4f" % p for p in phis))
    for d in [4, 6, 8, 10, 12, 16]:
        print("%-4d " % d + "  ".join("%-10.4f" % gamma_asym(d, p) for p in phis))
    print()
    print("finite n, failure <= 2^-129: least gamma with a0 = 0 / with a0 = 16; Delta of (W3)")
    for N in Ns:
        n = 2 ** N
        for d in ds:
            row = []
            for p in phis:
                g0 = gamma_min(n, d, p, 0)
                g16 = gamma_min(n, d, p, 16)
                row.append("%s/%s" % ("none" if g0 is None else "%.3f" % g0, "none" if g16 is None else "%.3f" % g16))
            print("N=%2d d=%2d  " % (N, d) + "  ".join("%-12s" % r for r in row) + "  Delta=%d" % delta_w3(n, d))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
