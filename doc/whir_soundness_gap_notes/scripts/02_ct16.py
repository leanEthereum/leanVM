"""Common-top classes, exhaustive, for n = 16 (N = 4).

For every subset S of D and every t, the key is (e_1(S), ..., e_t(S)), the top t coefficients of the locator below
the leading one. cmax[T][t] = largest number of T-subsets sharing a key. A genuine list (degree < k) at agreement T
needs t = T - k; with degree slack l (degree <= k - 1 + l) it needs t = T - k - l.

usage: python3 02_ct16.py [m] [power|random:<seed>] [N]
"""
import sys, random
from collections import Counter, defaultdict
import importlib.util, os

spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)


def all_keys(F, pts, tmax):
    """e[S] = tuple (e_1..e_tmax) for every subset S (bitmask over pts)."""
    n = len(pts)
    e = [None] * (1 << n)
    e[0] = (0,) * tmax
    mul = F.mul
    for S in range(1, 1 << n):
        low = S & -S
        i = low.bit_length() - 1
        prev = e[S ^ low]
        s = pts[i]
        # multiply (1 + e_1 Z + ...) by (1 + s Z)
        new = [0] * tmax
        new[0] = prev[0] ^ s
        for j in range(1, tmax):
            new[j] = prev[j] ^ mul(prev[j - 1], s)
        e[S] = tuple(new)
    return e


def main():
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    mode = sys.argv[2] if len(sys.argv) > 2 else "power"
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    F = gf.GF(m)
    if mode == "power":
        basis = gf.power_basis(F, N)
    else:
        basis = gf.random_basis(F, N, random.Random(int(mode.split(":")[1])))
    pts = gf.span(basis)
    n = len(pts)
    tmax = n // 2
    e = all_keys(F, pts, tmax)
    by_size = defaultdict(list)
    for S in range(1 << n):
        by_size[bin(S).count("1")].append(S)
    print(f"# m={m} D={mode} N={N} n={n}; entry = max class size (number of classes of that size)")
    print("T\\t " + " ".join(f"{t:>12d}" for t in range(1, tmax + 1)))
    best = {}
    for T in range(1, n):
        row = []
        for t in range(1, tmax + 1):
            if t >= T:
                row.append("-")
                continue
            cnt = Counter(e[S][:t] for S in by_size[T])
            mx = max(cnt.values())
            num = sum(1 for v in cnt.values() if v == mx)
            best[(T, t)] = (mx, num)
            row.append(f"{mx}({num})")
        print(f"{T:>3d} " + " ".join(f"{c:>12s}" for c in row))
    return F, pts, e, by_size, best


if __name__ == "__main__":
    main()
