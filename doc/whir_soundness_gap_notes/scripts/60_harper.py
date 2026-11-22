#!/usr/bin/env python3
"""Note 60: Harper's vertex-isoperimetric function of the N-cube, exactly.

NI(N, a)   = min over |A| = a of |N[A]|  (closed neighbourhood), by Harper's theorem
             = |B(r+1)| + KK_{N-r-1}(j) for a = |B(r)| + j, 0 <= j <= C(N, r+1).
iota(N, f) = max |int F| over |F| = f = max{a : NI(a) <= f}.
Gamma(N, rho) = max over a with NI(a) <= rho*n - 1 of  a/NI(a) - NI(a)/n
             (the fractional bound on (total interior - m)/n, see the note, Theorem 2.3).

Modes:
  python3 60_harper.py check      brute force check of NI for N <= 4 (all subsets)
  python3 60_harper.py table      sigma_frac(N, rho) for N = 10..28
  python3 60_harper.py profile N  the bound as a function of phi = m/n
  python3 60_harper.py blocks     boundary function h_t(a) of the block cubes t = 3..10
"""
import sys
from math import comb, log2
from fractions import Fraction


def ball(N, r):
    return sum(comb(N, i) for i in range(0, r + 1)) if r >= 0 else 0


def kk(j, s):
    """Kruskal-Katona: minimal lower shadow of j sets of size s (cascade)."""
    out = 0
    while j > 0 and s >= 1:
        a = s
        while comb(a + 1, s) <= j:
            a += 1
        out += comb(a, s - 1)
        j -= comb(a, s)
        s -= 1
    return out


def NI(N, a):
    """min |N[A]| over |A| = a in the N-cube (Harper)."""
    if a == 0:
        return 0
    r = 0
    tot = 1
    # largest r with |B(r)| <= a
    while r < N and tot + comb(N, r + 1) <= a:
        r += 1
        tot += comb(N, r)
    j = a - tot
    if r == N:
        return 2 ** N
    base = tot + comb(N, r + 1)  # |B(r+1)|
    if j == 0:
        return base
    # j sets of size r+1; upper shadow = lower shadow of complements (size N-r-1)
    return base + kk(j, N - r - 1)


def iota(N, f):
    """max a with NI(a) <= f (NI is nondecreasing)."""
    lo, hi = 0, 2 ** N
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if NI(N, mid) <= f:
            lo = mid
        else:
            hi = mid - 1
    return lo


def brute_check(N):
    n = 1 << N
    best = [None] * (n + 1)
    for A in range(1 << n):
        nb = A
        for i in range(N):
            # flip bit i of every vertex index
            lo = 0
            step = 1 << i
            # vertices with bit i = 0 are those v with (v >> i) & 1 == 0
            # build masks once
            nb |= shift(A, i, N)
        c = bin(A).count("1")
        d = bin(nb).count("1")
        if best[c] is None or d < best[c]:
            best[c] = d
    return best


_MASK = {}


def shift(A, i, N):
    key = (i, N)
    if key not in _MASK:
        n = 1 << N
        m0 = 0
        for v in range(n):
            if not (v >> i) & 1:
                m0 |= 1 << v
        _MASK[key] = m0
    m0 = _MASK[key]
    s = 1 << i
    return ((A & m0) << s) | ((A >> s) & m0)


def gamma_exact(N, cap, plus=0):
    """max over a >= 1 with NI(a) <= cap of (a+plus)/NI(a) - NI(a)/n, exact scan."""
    n = 2 ** N
    best = (Fraction(-1), 0, 0)
    a = 1
    while a <= n:
        f = NI(N, a)
        if f > cap:
            break
        v = Fraction(a + plus, f) - Fraction(f, n)
        if v > best[0]:
            best = (v, a, f)
        a += 1
    return best


def gamma_bound(N, cap, plus=0, tol=1e-7):
    """Rigorous upper bound (and a lower bound) on
    max over a with NI(a) <= cap of (a+plus)/NI(a) - NI(a)/n,
    by adaptive subdivision: on [a1, a2], value <= (a2+plus)/NI(a1) - NI(a1)/n."""
    n = 2 ** N
    amax = iota(N, cap)
    if amax < 1:
        return (-1.0, -1.0, 0, 0)

    def val(a):
        f = NI(N, a)
        return (a + plus) / f - f / n, f

    lb, arg, farg = -1.0, 0, 0
    # seed lower bound at ball sizes and at amax
    seeds = [amax]
    r = 0
    while ball(N, r) <= amax:
        seeds.append(ball(N, r))
        r += 1
    for a in seeds:
        v, f = val(a)
        if v > lb:
            lb, arg, farg = v, a, f
    ub = lb
    stack = [(1, amax)]
    evals = 0
    while stack:
        a1, a2 = stack.pop()
        f1 = NI(N, a1)
        evals += 1
        v1 = (a1 + plus) / f1 - f1 / n
        if v1 > lb:
            lb, arg, farg = v1, a1, f1
        if a1 == a2:
            ub = max(ub, v1)
            continue
        u = (a2 + plus) / f1 - f1 / n
        if u <= lb + tol:
            ub = max(ub, min(u, lb + tol))
            continue
        mid = (a1 + a2) // 2
        stack.append((a1, mid))
        stack.append((mid + 1, a2))
    return (lb, max(ub, lb), arg, farg, evals)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "table"
    if mode == "check":
        for N in (1, 2, 3, 4):
            b = brute_check(N)
            ok = all(b[a] == NI(N, a) for a in range(1, 2 ** N + 1))
            print(f"N={N}: brute force min |N[A]| by size equals Harper/KK formula: {ok}")
            if N <= 3:
                print("   NI:", [NI(N, a) for a in range(1, 2 ** N + 1)])
        # exact scan against adaptive bound
        for N in (8, 10, 12, 14):
            for rho in (2, 4, 8):
                cap = 2 ** N // rho - 1
                ex = gamma_exact(N, cap)
                bd = gamma_bound(N, cap)
                print(f"N={N} rho=1/{rho}: exact {float(ex[0]):.6f} at a={ex[1]} f={ex[2]}; adaptive [{bd[0]:.6f}, {bd[1]:.6f}] evals {bd[4]}")
        return
    if mode == "table":
        print("Fractional Harper bound: Gamma(N,rho) = max_{f <= rho n - 1} (iota(f)/f - f/n), sigma_frac = rho - Gamma")
        print("N | rho=1/2: Gamma_lo Gamma_hi sigma  argmax f/n (a/f) | rho=1/4: Gamma sigma | rho=1/8: Gamma sigma | rho=1/16: Gamma sigma")
        Ns = range(10, 29)
        if len(sys.argv) > 2:
            Ns = [int(x) for x in sys.argv[2:]]
        for N in Ns:
            n = 2 ** N
            row = [f"{N}"]
            for rho in (2, 4, 8, 16):
                cap = n // rho - 1
                lb, ub, a, f, ev = gamma_bound(N, cap, tol=2e-6)
                if rho == 2:
                    row.append(f"{lb:.5f} {ub:.5f} sigma>={0.5 - ub:.5f}  f/n={f / n:.4f} a/f={a / f:.4f}")
                else:
                    row.append(f"{ub:.5f} sigma>={1 / rho - ub:+.5f} (f/n={f / n:.4f})")
            print(" | ".join(row), flush=True)
        return
    if mode == "profile":
        N = int(sys.argv[2])
        n = 2 ** N
        print(f"N={N}: R(phi) = max_{{f <= phi n}} iota(f)/f (upper bound by adaptive search), and R(phi) - phi")
        for phi in (0.001, 0.002, 0.005, 0.01, 0.02, 0.03, 0.05, 0.0625, 0.08, 0.1, 0.125, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.4999999):
            cap = int(phi * n)
            # R(phi): maximize a/NI(a): use gamma machinery with n -> infinity trick: compute separately
            amax = iota(N, cap)
            best = 0.0
            # a/NI(a) is bounded on each layer segment by its right endpoint value bound; evaluate at ball sizes and amax
            r = 0
            cands = [amax]
            while ball(N, r) <= amax:
                cands.append(ball(N, r))
                r += 1
            for a in cands:
                if a >= 1:
                    best = max(best, a / NI(N, a))
            print(f"  phi={phi:.4f}: iota/n={amax / n:.5f}  R>={best:.5f}  R-phi>={best - phi:.5f}")
        return
    if mode == "blocks":
        for t in range(1, 11):
            n = 2 ** t
            h = [NI(t, a) - a for a in range(1, n + 1)]
            if t <= 5:
                print(f"t'={t}: h(a) for a=1..{n}: {h}")
            else:
                # summary: run-length of minimal values
                mn = min(h[: n - t - 1]) if n - t - 1 > 0 else None
                print(f"t'={t}: h(1)={h[0]}, h(2)={h[1]}, max h={max(h)} at a={h.index(max(h)) + 1}, min over 1<=a<=n-t-1: {mn}; last values h(n-5..n) = {h[-6:]}")
            # ratio table for the within-block fractional bound
            cand = [(a / NI(t, a), a) for a in range(1, n) if NI(t, a) < n]
            if cand:
                best = max(cand)
                print(f"      max a/|N[I_a]| over closures smaller than the block: {best[0]:.4f} at a={best[1]} (closure {NI(t, best[1])})")
        return


if __name__ == "__main__":
    main()
