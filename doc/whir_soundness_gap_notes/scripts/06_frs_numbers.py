"""Numbers for 06-capacity-codes.md: what a folded Reed-Solomon (FRS) level 0 would give leanVM's WHIR.

Level 0 at mu = 30: 2^6 lanes, each a polynomial of degree < 2^24, rate 2^-R. An m-folded level 0 keeps the
2^(24+R) evaluation points per lane but bundles m of them (x, gx, ..., g^(m-1) x) into one Merkle leaf, so it has
N = 2^(24+R)/m leaves of 64*m field elements.

Radius: the mutual correlated agreement theorem for tau-subspace-design codes in the form of
[LXYYZ26, Thm 4.14] (ePrint 2026/2133, refining [GG25]) with l = 1:
    radius < min( L/(L+1) * (1 - tau(L)),  1 - tau(s) - (2 - tau(s))/(s+1) ),   tau(r) = m*rho/(m-r+1),
    error  = (floor(radius*N + 1)*L + A) / |E|,  A = ceil((t1-1)(radius*(s-1)+e2)/e2) + 1,
    t1 = 1 + ceil(radius/e1), e1 = L/(L+1)(1-tau(L)) - radius, e2 = 1 - tau(s) - radius.
"""
from math import ceil, floor, log2, sqrt

KAPPA, LANES, QUERY_BITS, FIELD_BITS, TARGET = 24, 64, 108, 128, 125

def queries(bits_per_query):
    return ceil(QUERY_BITS / bits_per_query)

def tau_frs(m, rho, r):
    return m * rho / (m - r + 1) if r <= m else 1.0

def tau_opt(m, rho, r):  # no subspace-design code over E^m can do better: dim A_i >= dim A - m
    return max(rho, 1 - m / r)

def best_radius(m, rho, N, tau, max_grind=30):
    """Smallest provable symbol agreement threshold: (key, agreement count, L, s, grind bits, radius) or None."""
    span = range(1, int(2 * m / (1 - rho)) + 3)
    b_of = {s: 1 - tau(m, rho, s) - (2 - tau(m, rho, s)) / (s + 1) for s in span}
    a_of = {L: L / (L + 1) * (1 - tau(m, rho, L)) for L in span}
    best = None
    for s in sorted(span, key=lambda s: -b_of[s])[:3]:
        ts, b = tau(m, rho, s), b_of[s]
        for L in span:
            a = a_of[L]
            top = min(a, b)
            for margin in (0.002, 0.005, 0.01, 0.02):  # stay this far inside the radius condition
                rad = top - margin
                if rad <= 0:
                    continue
                e1, e2 = a - rad, 1 - ts - rad
                t1 = 1 + ceil(rad / e1)
                A = ceil((t1 - 1) * (rad * (s - 1) + e2) / e2) + 1
                num = floor(rad * N + 1) * L + A
                grind = max(0, ceil(log2(num) - FIELD_BITS + TARGET))
                if grind > max_grind:
                    continue
                agree = N - floor(rad * N)  # words agreeing on at least this many symbols are in the list
                key = (agree / N, grind)
                if best is None or key < best[0]:
                    best = (key, agree, L, s, grind, rad)
    return best

def level0_cost(m, R, t):
    """(proof bytes, Keccak permutations in the recursive verifier) of level 0's queries."""
    depth = KAPPA + R - int(log2(m))
    path = max(0, depth - int(log2(t)))  # Merkle pruning shares about log2(t) top levels
    leaf_bytes = 8 * LANES * m
    return t * (leaf_bytes + 32 * path), t * (ceil(leaf_bytes / 136) + path)

print("== plain interleaved RS (today), Johnson, and capacity")
print("rate   Johnson t   capacity t   level-0 KB   level-0 Keccaks")
base = {}
for R in (1, 2, 3, 4):
    rho = 2.0 ** -R
    tj, tc = queries(-log2(sqrt(rho))), queries(-log2(rho))
    kb, kec = level0_cost(1, R, tj)
    base[R] = (tj, kb, kec)
    print(f"1/{2**R:<3}  {tj:>9}   {tc:>10}   {kb/1024:>10.0f}   {kec:>15}")

for name, tau in (("FRS (tau = m rho/(m-r+1), [GK16])", tau_frs), ("best conceivable subspace design over E^m (tau = max(rho, 1-m/r))", tau_opt)):
    print(f"\n== {name}, MCA radius of [LXYYZ26, Thm 4.14]")
    print("rate   m     agree/N  bits/q   t    L    s   fold grind   KB vs today   Keccaks vs today")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        for m in (2, 4, 8, 16, 32, 64, 128, 256, 1024):
            N = 2 ** (KAPPA + R) // m
            r = best_radius(m, rho, N, tau)
            if r is None:
                print(f"1/{2**R:<3}  {m:<5} no admissible parameters")
                continue
            _, agree, L, s, grind, rad = r
            bits = log2(N / (agree - 1))
            t = queries(bits)
            kb, kec = level0_cost(m, R, t)
            tj, kb0, kec0 = base[R]
            print(f"1/{2**R:<3}  {m:<5} {agree/N:.4f}   {bits:.3f}  {t:>4} {L:>4} {s:>4}   {grind:>6}      x{kb/kb0:<8.2f}     x{kec/kec0:.2f}")

print("\n== list-decoding radius alone, [CZ25]: L/(L+1) (1 - m rho/(m-L+1)) (no MCA at this radius is proven)")
print("rate   m     best agree/N   L    t")
for R in (1, 2, 3, 4):
    rho = 2.0 ** -R
    for m in (16, 64, 256, 1024):
        rad, L = max((L / (L + 1) * (1 - tau_frs(m, rho, L)), L) for L in range(1, m + 1))
        print(f"1/{2**R:<3}  {m:<5} {1-rad:.4f}        {L:>4} {queries(-log2(1 - rad)):>4}")

print("\n== random RS, [AGL24, Thm 1.1]: radius L/(L+1)(1-rho-eta) needs |F| >= n + k 2^(10 L/eta)")
for field_bits, where in ((64, "points in K"), (128, "points in E")):
    for R in (1, 4):
        rho, k_bits = 2.0 ** -R, KAPPA
        budget = field_bits - k_bits  # 10 L / eta <= budget
        best = max(((L / (L + 1)) * (1 - rho - 10 * L / budget), L) for L in range(1, 20))
        print(f"{where}, rate 1/{2**R}: best proven radius {max(best[0], 0):.3f} (L = {best[1]}), Johnson {1 - sqrt(rho):.3f}")
