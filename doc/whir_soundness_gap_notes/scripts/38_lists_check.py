"""Note 38, section 3: the nested half-support families. Checks
  (1) |Q_2(X)| = (2^m-1)(2^m-2)(2^(m+1)-8)/6 + 2^(m+1)-2 by brute force, m = 3, 4, 5;
  (2) rate 1/2, c = 3, N = 5: all 3*q_1(3)*q_2(4) = 36540 members are distinct and share the top of X^16 L_P;
  (3) random members at rate 1/2 (c = 3, 4, 5), 1/4 (c = 2, 3), 1/8 (c = 2, 3): deg(L_S + X^k L_P) <= k.
Sets are bitmasks over the indices 0..2^N-1; index i is the field element with bit pattern i."""
import random, sys, importlib
sys.path.insert(0, sys.path[0])
gfm = importlib.import_module("38_gf")
random.seed(38)
par = lambda v: bin(v).count("1") & 1


def Q2_formula(m):
    return (2**m - 1) * (2**m - 2) * (2 ** (m + 1) - 8) // 6 + 2 ** (m + 1) - 2


def Q2_brute(m):
    """all unions of flats of codimension <= 2 of F_2^m of total size 2^(m-1), as masks"""
    out = set()
    pts = range(1 << m)
    for a in range(1, 1 << m):
        for c in (0, 1):
            out.add(sum(1 << x for x in pts if par(a & x) == c))
    for phi in range(1, 1 << m):
        half = [[x for x in pts if par(phi & x) == b] for b in (0, 1)]
        hyp = [set(), set()]
        for b in (0, 1):
            for psi in range(1, 1 << m):
                if psi == phi:
                    continue
                for c in (0, 1):
                    hyp[b].add(sum(1 << x for x in half[b] if par(psi & x) == c))
        for A0 in hyp[0]:
            for A1 in hyp[1]:
                out.add(A0 | A1)
    return out


def cube(N, fixmask, fixval):
    return [x for x in range(1 << N) if x & fixmask == fixval]


def all_Q1(X, free):
    """affine hyperplanes of the coordinate cube X with free coordinate mask `free`"""
    res = set()
    sub = free
    while sub:
        for c in (0, 1):
            res.add(sum(1 << x for x in X if par(sub & x) == c))
        sub = (sub - 1) & free
    return res


def all_Q2(X, free):
    res = set(all_Q1(X, free))
    subs = []
    s = free
    while s:
        subs.append(s)
        s = (s - 1) & free
    for phi in subs:
        halves = [[x for x in X if par(phi & x) == b] for b in (0, 1)]
        hyp = [set(), set()]
        for b in (0, 1):
            for psi in subs:
                if psi != phi:
                    for c in (0, 1):
                        hyp[b].add(sum(1 << x for x in halves[b] if par(psi & x) == c))
        for A0 in hyp[0]:
            for A1 in hyp[1]:
                res.add(A0 | A1)
    return res


def rand_fn(free, avoid=()):
    while True:
        a = random.getrandbits(free.bit_length()) & free
        if a and a not in avoid:
            return a


def sample_Q(N, fixmask, fixval, c):
    """random member of Q_c of the coordinate cube: fixed top splits down to height 2, free splits below"""
    free = ((1 << N) - 1) & ~fixmask
    X = cube(N, fixmask, fixval)
    if c == 1:
        a, b = rand_fn(free), random.getrandbits(1)
        return sum(1 << x for x in X if par(a & x) == b)
    if c == 2:
        phi = rand_fn(free)
        m = 0
        for b in (0, 1):
            psi, cc = rand_fn(free, (phi,)), random.getrandbits(1)
            m |= sum(1 << x for x in X if par(phi & x) == b and par(psi & x) == cc)
        return m
    top = 1 << (free.bit_length() - 1)
    return sample_Q(N, fixmask | top, fixval, c - 1) | sample_Q(N, fixmask | top, fixval | top, c - 1)


def sample_half(N, c):
    """rate 1/2: S = P + A, A in Q_c(D; P), P the cube with the c+1 top coordinates zero. Returns (P, A)."""
    fixmask = fixval = 0
    A = 0
    for i in range(c - 1, 0, -1):          # free Q_i in the half with the next top bit = 1
        top = 1 << (N - (c - i))
        A |= sample_Q(N, fixmask | top, fixval | top, i)
        fixmask |= top
    # now the cube of dimension N-c+1 with the top c-1 bits zero; P has two more bits zero
    b1, b2 = 1 << (N - c), 1 << (N - c - 1)
    X = cube(N, fixmask, 0)
    a = random.choice([b1, b2, b1 | b2])
    A |= sum(1 << x for x in X if par(a & x) == 1)
    P = sum(1 << x for x in cube(N, fixmask | b1 | b2, 0))
    return P, A


def check_top(F, N, P, A, k):
    pts = lambda m: [x for x in range(1 << N) if m >> x & 1]
    assert P & A == 0
    LS = F.locator(pts(P | A))
    W = [0] * k + F.locator(pts(P))
    return gfm.deg(gfm.padd(LS, W)) <= k


if __name__ == "__main__":
    for m in (3, 4, 5):
        b = Q2_brute(m)
        assert all(bin(x).count("1") == 1 << (m - 1) for x in b)
        print(f"(1) m={m}: brute {len(b)}  formula {Q2_formula(m)}  {'OK' if len(b)==Q2_formula(m) else 'MISMATCH'}")

    # (2) full enumeration, N = 5, c = 3, n = 32, k = 16, agreement 18
    N, F = 5, gfm.GF(10)
    q2 = all_Q2(cube(N, 16, 16), 15)                 # half with bit4 = 1, dimension 4
    q1 = all_Q1(cube(N, 16 | 8, 8), 7)               # bit4 = 0, bit3 = 1, dimension 3
    X00 = cube(N, 24, 0)
    last = [sum(1 << x for x in X00 if par(a & x) == 1) for a in (4, 2, 6)]
    P = sum(1 << x for x in cube(N, 24 | 6, 0))
    fam = {a | b | c for a in q2 for b in q1 for c in last}
    want = 3 * (2**4 - 2) * Q2_formula(4)
    ok = all(check_top(F, N, P, A, 16) for A in fam)
    print(f"(2) N=5 c=3: |Q_2(4)|={len(q2)} |Q_1(3)|={len(q1)} members {len(fam)} (formula {want}), "
          f"all |S|=18: {all(bin(A|P).count('1')==18 for A in fam)}, all share the top above degree 16: {ok}")

    # (3) random members
    for N, c, m in ((6, 3, 12), (7, 3, 12), (7, 4, 12), (8, 4, 12), (8, 5, 12)):
        F, k = gfm.GF(m), 1 << (N - 1)
        good = sum(check_top(F, N, *sample_half(N, c), k) for _ in range(60))
        print(f"(3) rate 1/2 N={N} c={c}: agreement {k + (1 << (N - c - 1))}/{1 << N}, {good}/60 members with deg(L_S + X^k L_P) <= k")
    for R, N, c, m in ((2, 7, 2, 12), (2, 7, 3, 12), (2, 8, 3, 12), (3, 8, 2, 12), (3, 8, 3, 12), (4, 9, 2, 12)):
        F, k = gfm.GF(m), 1 << (N - R)
        g = k >> c
        good = 0
        for _ in range(40):
            top = 1 << (N - 1)
            fix = sum(1 << (N - 1 - i) for i in range(R - 1))        # X: top R-1 bits fixed, top bit = 1
            val = top | (random.getrandbits(N) & fix)
            A = sample_Q(N, fix, val, c)
            H0 = [x for x in range(1 << N) if not x & top]
            P = sum(1 << x for x in random.sample(H0, g))
            good += check_top(F, N, P, A, k)
        print(f"(3) rate 2^-{R} N={N} c={c}: agreement {k+g}/{1<<N} = rho(1+2^-{c}), arbitrary padding of {g} points: {good}/40 OK")
