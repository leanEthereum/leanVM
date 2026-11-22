"""Researcher 05: the rate-1/2 family at agreement 5n/8 (Theorem 2 of 05-constructions.md) and the 9n/16 stack.

Checks, on D_N = span(1, x, .., x^(N-1)) inside GF(2^16):
  1. enumerate the whole class F_W (disjoint unions of flats, each a coset of the fixed codimension-3 subspace W or a
     flat of size >= n/4) of size 5n/8, count it, and check that every member's locator agrees with X^(n/2) L_W in all
     coefficients of degree > n/2;
  2. the count against the closed formula;
  3. for a random sample at larger N, the same top check;
  4. the 9n/16 stack (three free hyperplanes of three quarters plus a fixed set).
Run: python3 05_check_five_eighths.py [Nmax]   (default 7; N = 7 takes about a minute)
"""
import random
import sys
from itertools import combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import importlib

gfm = importlib.import_module("05_gf")
GF, span, subspaces_by_codim, kernel_basis, parity = gfm.GF, gfm.span, gfm.subspaces_by_codim, gfm.kernel_basis, gfm.parity

F = GF(16)


def mask_of(pts):
    m = 0
    for p in pts:
        m |= 1 << p
    return m


def pts_of(mask):
    out = []
    i = 0
    while mask:
        if mask & 1:
            out.append(i)
        mask >>= 1
        i += 1
    return out


def top_coeffs(pts, K):
    """Coefficients of degree > K of the locator, as a tuple (degree K+1 .. T)."""
    return tuple(F.locator(pts)[K + 1:])


def reference_top(N):
    """X^(n/2) * L_W above degree n/2, W = span(1..x^(N-4))."""
    n = 1 << N
    LW = F.subspace_poly([1 << i for i in range(N - 3)])
    T = 5 * n // 8
    top = [0] * (T + 1)
    for j, cj in enumerate(LW):
        top[n // 2 + (1 << j)] ^= cj
    return tuple(top[n // 2 + 1:])


def enumerate_class(N):
    n = 1 << N
    w = N - 3
    cos = [mask_of(range(a << w, (a + 1) << w)) for a in range(8)]
    flats = []
    for funcs in subspaces_by_codim(N, 2):
        base = mask_of(span(kernel_basis(N, funcs)))
        f1, f2 = funcs
        # translates: one representative per value of (f1, f2)
        reps = {}
        for v in range(n):
            key = (parity(v & f1), parity(v & f2))
            if key not in reps:
                reps[key] = v
                if len(reps) == 4:
                    break
        for v in reps.values():
            m = 0
            for p in pts_of(base):
                m |= 1 << (p ^ v)
            flats.append(m)
    members = set()
    for c5 in combinations(range(8), 5):
        m = 0
        for a in c5:
            m |= cos[a]
        members.add(m)
    usable = []
    for fl in flats:
        free = [a for a in range(8) if cos[a] & fl == 0]
        if free:
            usable.append((fl, free))
        for c3 in combinations(free, 3):
            members.add(fl | cos[c3[0]] | cos[c3[1]] | cos[c3[2]])
    for i in range(len(usable)):
        f1, free1 = usable[i]
        for j in range(i + 1, len(usable)):
            f2, free2 = usable[j]
            if f1 & f2:
                continue
            for a in free1:
                if a in free2:
                    members.add(f1 | f2 | cos[a])
    return members


_HM = {}


def hyper_masks(N):
    if N not in _HM:
        _HM[N] = [mask_of([v for v in range(1 << N) if parity(v & phi)]) for phi in range(1, 1 << N)]
    return _HM[N]


def check_class(N):
    n = 1 << N
    members = enumerate_class(N)
    ref = reference_top(N)
    bad = 0
    sample = members if N <= 6 else random.sample(sorted(members), 300)
    for m in sample:
        pts = pts_of(m)
        assert len(pts) == 5 * n // 8
        if top_coeffs(pts, n // 2) != ref:
            bad += 1
    with0 = sum(1 for m in members if m & 1)
    # Lemma 6.2 of the report with g = n/8: hyperplane counts agree modulo n/8 across the class
    sigs = set()
    for m in (members if N <= 6 else sample):
        sigs.add(tuple(bin(m & hmask).count("1") % (n // 8) for hmask in hyper_masks(N)))
    assert len(sigs) == 1, "hyperplane counts are not constant modulo n/8"
    print(f"N={N}: |F_W| = {len(members)}, containing 0: {with0}, top mismatches in {len(sample)} checked: {bad}, "
          f"formula 56*(2^N - 7) = {56 * (n - 7)}, 35*(2^N - 7) = {35 * (n - 7)}")
    return len(members)


def random_hyperplane_flat(Npts_basis, offset, rng):
    """A random affine hyperplane of the flat offset + span(basis)."""
    k = len(Npts_basis)
    while True:
        phi = rng.randrange(1, 1 << k)
        break
    c = rng.randrange(2)
    pts = []
    for coords in range(1 << k):
        if parity(coords & phi) == c:
            v = offset
            for i in range(k):
                if (coords >> i) & 1:
                    v ^= Npts_basis[i]
            pts.append(v)
    return pts


def check_sample(N, trials, rng):
    """S = P u F: P = three cosets of W in the half {top bit 0}, F a random affine hyperplane of the other half."""
    n = 1 << N
    w = N - 3
    ref = reference_top(N)
    half_basis = [1 << i for i in range(N - 1)]
    bad = 0
    for _ in range(trials):
        c3 = rng.sample(range(4), 3)
        P = [p for a in c3 for p in range(a << w, (a + 1) << w)]
        Fl = random_hyperplane_flat(half_basis, 1 << (N - 1), rng)
        S = P + Fl
        assert len(set(S)) == 5 * n // 8
        if top_coeffs(S, n // 2) != ref:
            bad += 1
    print(f"N={N}: {trials} random members P u F, top mismatches: {bad}")


def check_arbitrary_P(N, trials, rng):
    """Theorem 2 with an arbitrary fixed P (not a union of cosets): tops agree among members with the same P."""
    n = 1 << N
    half_basis = [1 << i for i in range(N - 1)]
    P = rng.sample(range(n // 2), 3 * n // 8)
    tops = set()
    for _ in range(trials):
        Fl = random_hyperplane_flat(half_basis, 1 << (N - 1), rng)
        tops.add(top_coeffs(P + Fl, n // 2))
    print(f"N={N}: arbitrary fixed P of size 3n/8, {trials} free hyperplanes of the other half, distinct tops: {len(tops)}")


def check_stack(N, trials, rng):
    """9n/16: fixed P of 3n/16 points in quarter 0, one free affine hyperplane in each of quarters 1, 2, 3."""
    n = 1 << N
    qb = [1 << i for i in range(N - 2)]
    P = rng.sample(range(n // 4), 3 * n // 16)
    tops = set()
    for _ in range(trials):
        S = list(P)
        for z in (1, 2, 3):
            S += random_hyperplane_flat(qb, z << (N - 2), rng)
        assert len(set(S)) == 9 * n // 16
        tops.add(top_coeffs(S, n // 2))
    print(f"N={N}: 9n/16 stack, {trials} random members, distinct tops above degree n/2: {len(tops)}")


if __name__ == "__main__":
    rng = random.Random(5)
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for N in range(5, nmax + 1):
        check_class(N)
    for N in (8, 9):
        check_sample(N, 40, rng)
        check_arbitrary_P(N, 20, rng)
    for N in (6, 8):
        check_stack(N, 30, rng)


def check_duality(N):
    """Complements of the class F_W: sets of size 3n/8 whose locators share the top of X^(n/4) L_W above degree n/4
    (rate 1/4, agreement 3n/8), as Proposition 1.3 of the report predicts."""
    n = 1 << N
    members = sorted(enumerate_class(N))
    LW = F.subspace_poly([1 << i for i in range(N - 3)])
    T = 3 * n // 8
    top = [0] * (T + 1)
    for j, cj in enumerate(LW):
        top[n // 4 + (1 << j)] ^= cj
    ref = tuple(top[n // 4 + 1:])
    full = (1 << n) - 1
    step = max(1, len(members) // 200)
    bad = sum(1 for m in members[::step] if top_coeffs(pts_of(full ^ m), n // 4) != ref)
    print(f"N={N}: complements of F_W (size 3n/8), top of X^(n/4) L_W above degree n/4, mismatches in "
          f"{len(members[::step])} checked: {bad}")


if __name__ == "__main__":
    check_duality(6)
