# Researcher 21 (referee). Independent checks of the attack-side claims (flats, the 5n/8 class, its genuine and slack variants,
# Theorem W on a random domain, exact classes at n = 32 by meet in the middle on real-shape and random domains).
# Usage: python3 21_attack_checks.py flats | thmw | five8 [Nmax] | mitm | extra | all
import itertools
import random
import sys
from math import comb

sys.dont_write_bytecode = True
import importlib

gf = importlib.import_module("21_gf")
F = gf.K64


def gauss_binom(n, k):
    num = den = 1
    for i in range(k):
        num *= (1 << (n - i)) - 1
        den *= (1 << (i + 1)) - 1
    return num // den


def subspaces_of_dim(N, s):
    """All s-dimensional subspaces of F_2^N as reduced echelon bases (bit masks)."""
    out = []
    for piv in itertools.combinations(range(N), s):
        free = [[j for j in range(p) if j not in piv] for p in piv]
        for vals in itertools.product(*[range(1 << len(f)) for f in free]):
            basis = []
            for p, f, v in zip(piv, free, vals):
                b = 1 << p
                for i, j in enumerate(f):
                    if v >> i & 1:
                        b |= 1 << j
                basis.append(b)
            out.append(basis)
    return out


def check_flats():
    # Flats lemma: for V <= D of size 2^s, Q_V = (L_V - X^(2^s))/X has degree 2^(s-1) - 1 and equals x^(2^s - 1) on V \ 0.
    for N, R in ((7, 2), (7, 3), (8, 2), (8, 4)):
        n, kappa = 1 << N, N - R
        k, s = 1 << kappa, kappa + 1
        D = gf.span(gf.power_basis(N))  # leanVM shape: D[i] = the polynomial with bit mask i
        subs = subspaces_of_dim(N, s)
        assert len(subs) == gauss_binom(N, R - 1)
        rng = random.Random(N * 10 + R)
        sample = subs if len(subs) <= 300 else rng.sample(subs, 60)
        seen = set()
        for basis in sample:
            c = gf.lin_poly(F, basis)  # L_V = sum c[j] X^(2^j), c[s] = 1
            assert len(c) == s + 1 and c[s] == 1
            # Q_V = sum_{j<s} c[j] X^(2^j - 1): degree 2^(s-1) - 1 = k - 1 < k, so a genuine codeword
            Vset = set(gf.span(basis))
            agree = 0
            for x in D:
                if x == 0:
                    continue
                q = gf.lin_eval(F, c[:s], x)  # = Q_V(x) * x
                w = F.pow(x, (1 << s) - 1)  # the word x^(2^s - 1)
                a = (q == F.mul(w, x))  # compare after multiplying by x != 0
                assert a == (x in Vset)
                agree += a
            assert agree == (1 << s) - 1 == 2 * k - 1
            seen.add(tuple(c))
        assert len(seen) == len(sample)
        print(f"flats N={N} rate 1/{1 << R}: {len(subs)} subspaces of size 2k (Gaussian binomial ok), {len(sample)} checked: "
              f"Q_V of degree k-1 agrees with x^(2k-1) exactly on V\\0 ({2 * k - 1} points); on D\\V never; all Q_V distinct")


def walsh_key(pts_idx, mult, N, mod):
    key = []
    for phi in range(1, 1 << N):
        c = 0
        for i, mu in zip(pts_idx, mult):
            if bin(i & phi).count("1") & 1:
                c += mu
        key.append(c % mod)
    return tuple(key)


def check_thmw():
    rng = random.Random(2021)
    # (a) sets, N = 4, random basis in K: partition by (e_1..e_t) equals partition by (n_phi mod 2^(a+1)), 2^a <= t < 2^(a+1)
    N = 4
    basis = gf.random_basis(F, N, rng)
    D = gf.span(basis)
    n = 1 << N
    tmax = 7
    recs = {}
    for S in range(1 << n):
        idx = [i for i in range(n) if S >> i & 1]
        T = len(idx)
        recs.setdefault(T, []).append((S, idx))
    cells = 0
    for T, lst in recs.items():
        es = {}
        for S, idx in lst:
            es[S] = gf.top_coeffs(F, [D[i] for i in idx], tmax)
        for t in range(1, tmax + 1):
            a = t.bit_length() - 1
            mod = 1 << (a + 1)
            m1, m2 = {}, {}
            ok = True
            for S, idx in lst:
                ke = tuple(es[S][1:t + 1])
                kw = walsh_key(idx, [1] * T, N, mod)
                if m1.setdefault(ke, kw) != kw or m2.setdefault(kw, ke) != ke:
                    ok = False
            assert ok, (T, t)
            cells += 1
    print(f"Theorem W and converse, sets: N=4, random basis in GF(2^64), all T, t<=7: {cells} cells, partitions equal")
    # the forward direction must hold on every domain: test it on the power shape and in a small field
    for name, Fd, Dd in (("power shape, K", F, gf.span(gf.power_basis(4))), ("GF(16)", gf.small_field(4), list(range(16)))):
        bad = 0
        for T, lst in recs.items():
            es = {S: gf.top_coeffs(Fd, [Dd[i] for i in idx], tmax) for S, idx in lst}
            for t in (1, 3, 7):
                a = t.bit_length() - 1
                m2 = {}
                for S, idx in lst:
                    kw = walsh_key(idx, [1] * T, 4, 1 << (a + 1))
                    ke = tuple(es[S][1:t + 1])
                    if m2.setdefault(kw, ke) != ke:
                        bad += 1
        assert bad == 0
        print(f"  forward direction (Walsh congruent => common top) on {name}: no violation")
    # (b) multisets, N = 3, multiplicities <= 4 on the 7 nonzero points, random basis: both directions, equal mass
    N = 3
    basis = gf.random_basis(F, N, rng)
    D = gf.span(basis)
    bymass = {}
    for mult in itertools.product(range(5), repeat=7):
        bymass.setdefault(sum(mult), []).append(mult)
    cells = 0
    for mass, lst in bymass.items():
        es = {}
        for mult in lst:
            pts = []
            for i, mu in enumerate(mult):
                pts += [D[i + 1]] * mu
            es[mult] = gf.top_coeffs(F, pts, tmax)
        for t in range(1, tmax + 1):
            a = t.bit_length() - 1
            mod = 1 << (a + 1)
            m1, m2 = {}, {}
            for mult in lst:
                ke = tuple(es[mult][1:t + 1])
                kw = walsh_key(range(1, 8), mult, N, mod)
                assert m1.setdefault(ke, kw) == kw and m2.setdefault(kw, ke) == ke, (mass, t)
            cells += 1
    print(f"Theorem W and converse, multisets: N=3, multiplicities <=4, all masses, t<=7: {cells} cells, partitions equal")
    # (c) multisets, N = 4, multiplicities <= 2, mass <= 7
    N = 4
    basis = gf.random_basis(F, N, rng)
    D = gf.span(basis)
    bymass = {}

    def rec(i, mult, mass):
        if i == 16:
            bymass.setdefault(mass, []).append(tuple(mult))
            return
        for mu in range(3):
            if mass + mu <= 7:
                mult.append(mu)
                rec(i + 1, mult, mass + mu)
                mult.pop()

    rec(1, [], 0)
    cells = 0
    tot = 0
    for mass, lst in bymass.items():
        tot += len(lst)
        es = {}
        for mult in lst:
            pts = []
            for i, mu in enumerate(mult):
                pts += [D[i + 1]] * mu
            es[mult] = gf.top_coeffs(F, pts, tmax)
        for t in (1, 2, 3, 4, 7):
            a = t.bit_length() - 1
            mod = 1 << (a + 1)
            m1, m2 = {}, {}
            for mult in lst:
                ke = tuple(es[mult][1:t + 1])
                kw = walsh_key(range(1, 16), mult, N, mod)
                assert m1.setdefault(ke, kw) == kw and m2.setdefault(kw, ke) == ke, (mass, t)
            cells += 1
    print(f"Theorem W and converse, multisets: N=4, multiplicities <=2, mass <=7 ({tot} multisets), t in 1,2,3,4,7: {cells} cells, partitions equal")


def five8_family(N, Ubasis_idx):
    """The class of L_U^5 in two independent descriptions, as frozensets of point indices of F_2^N.
    Ubasis_idx: N-3 independent vectors (bit masks). Returns (famA, famB)."""
    n = 1 << N
    U = set(gf.span(Ubasis_idx))
    assert len(U) == n // 8
    # description B (note 05): disjoint unions of flats, each a coset of U or of size >= n/4, total 5n/8:
    #   (a) five cosets of U; (b) F + three cosets of U, F a flat of size n/4 whose direction does not contain U.
    cos = {}
    for x in range(n):
        cos.setdefault(min(x ^ u for u in U), set()).add(x)
    cosets = [frozenset(c) for c in cos.values()]
    assert len(cosets) == 8
    famB = set()
    for five in itertools.combinations(cosets, 5):
        famB.add(frozenset().union(*five))
    nb_a = len(famB)
    for basis in subspaces_of_dim(N, N - 2):
        V = set(gf.span(basis))
        if U <= V:
            continue
        reps = {min(x ^ v for v in V) for x in range(n)}
        for r in reps:
            Fl = frozenset(x ^ r for x in V)
            free = [c for c in cosets if not (c & Fl)]
            for three in itertools.combinations(free, 3):
                famB.add(Fl.union(*three))
    # description A (note 02): for each hyperplane W of U, unions of ten cosets of W with label sum eta_W (abstractly:
    # label space = F_2^N / W, eta = image of U; the sum of the ten labels must be the nonzero element of U/W).
    famA = set()
    Ub = list(Ubasis_idx)
    for hyp in subspaces_of_dim(len(Ub), len(Ub) - 1):
        Wb = []
        for h in hyp:
            v = 0
            for j in range(len(Ub)):
                if h >> j & 1:
                    v ^= Ub[j]
            Wb.append(v)
        W = set(gf.span(Wb)) if Wb else {0}
        cw = {}
        for x in range(n):
            cw.setdefault(min(x ^ w for w in W), set()).add(x)
        labs = sorted(cw)  # coset representatives (minimal elements): the label of x is min(x + W)
        eta = min(u for u in U if u not in W)
        eta_lab = min(eta ^ w for w in W)
        for ten in itertools.combinations(labs, 10):
            sx = 0
            for l in ten:
                sx ^= l
            if min(sx ^ w for w in W) == eta_lab:
                famA.add(frozenset().union(*[cw[l] for l in ten]))
    return famA, famB, nb_a, cosets


def check_five8(Nmax):
    rng = random.Random(58)
    for N in range(5, Nmax + 1):
        n = 1 << N
        # U: random subspace of dimension N-3 of F_2^N (indices); the field embedding is the power shape and a random basis
        while True:
            Ub = [rng.randrange(1, n) for _ in range(N - 3)]
            if len(set(gf.span(Ub))) == n // 8:
                break
        famA, famB, nb_a, cosets = five8_family(N, Ub)
        assert famA == famB, (len(famA), len(famB))
        assert len(famA) == 56 * n - 392
        assert all(len(S) == 5 * n // 8 for S in famA)
        p = rng.randrange(n)
        through = sum(1 for S in famA if p in S)
        assert through == 35 * n - 245
        # slack family: members avoiding one coset of U
        c0 = cosets[0]
        avoid = sum(1 for S in famA if not (S & c0))
        assert avoid == 7 * n - 35
        print(f"5n/8 class N={N}: the two descriptions (note 02: ten cosets of a hyperplane of U; note 05: flat + three cosets) "
              f"give the same {len(famA)} sets = 56n-392; {through} = 35n-245 contain a given point; {avoid} = 7n-35 avoid a given coset of U")
        # tree count of [DKTZ26] as quoted in note 01: members containing one fixed coset of U ("padding"), minus hyperplane unions
        cont = [S for S in famA if c0 <= S]
        hyp_like = 0
        for S in cont:
            A = S - c0
            # is A (n/2 points) an affine hyperplane?
            a0 = min(A)
            tr = {x ^ a0 for x in A}
            piv = {}
            for x in tr:  # rank of tr: it is a subspace iff 2^rank = |tr|
                while x:
                    h = x.bit_length()
                    if h in piv:
                        x ^= piv[h]
                    else:
                        piv[h] = x
                        break
            if 1 << len(piv) == len(tr):
                hyp_like += 1
        print(f"   members containing one fixed coset of U: {len(cont)} = 21n-133 ({21 * n - 133}); of these {hyp_like} are coset + affine hyperplane;"
              f" the rest {len(cont) - hyp_like} = 21n-140 ({21 * n - 140}) = M_2(N) = {28 * (6 * (n // 8) - 5)}")
        assert len(cont) == 21 * n - 133 and len(cont) - hyp_like == 21 * n - 140 == 28 * (6 * (n // 8) - 5)
        # field check: common top of L_U^5 above degree n/2, on the leanVM shape and on a random domain in K
        for name, basis in (("power shape", gf.power_basis(N)), ("random basis", gf.random_basis(F, N, rng))):
            D = gf.span(basis)
            t = n // 8  # e_1..e_{n/8 - 1} shared, e_{n/8} not
            sample = list(famA) if N <= 6 else rng.sample(list(famA), 400)
            tops = {}
            for S in sample:
                e = gf.top_coeffs(F, [D[i] for i in S], t)
                tops.setdefault(tuple(e[1:t]), []).append(e[t])
            assert len(tops) == 1
            (top, lasts), = tops.items()
            # compare with the top of L_U^5 itself
            LU = gf.lin_poly(F, [D[b] for b in Ub])
            # reversed L_U: 1 + sum c_j Z^(|U| - 2^j); L_U^5 reversed mod Z^(t)
            # reversed L_U = sum_j c_j Z^(|U| - 2^j); its fifth power modulo Z^t gives e_1..e_(t-1) of the word L_U^5
            rev = [0] * t
            for j, cj in enumerate(LU):
                if (n // 8) - (1 << j) < t:
                    rev[(n // 8) - (1 << j)] ^= cj
            r5 = [1] + [0] * (t - 1)
            for _ in range(5):
                r5 = gf.poly_mul(F, r5, rev)[:t]
            assert list(top) == r5[1:t]
            print(f"   {name}: {len(sample)} members checked, all share e_1..e_(n/8-1) with the word L_U^5 (degree of L_U^5 - Z_S <= n/2);"
                  f" e_(n/8) takes {len(set(lasts))} values (so they are not all one genuine list at 5n/8)")
            # exact agreement of the word L_U^5 with P_S = L_U^5 - Z_S for a few members: P_S has degree <= n/2 and agreement exactly 5n/8
            for S in sample[:3]:
                ZS = gf.locator(F, [D[i] for i in S])
                LUfull = [0] * (n // 8 + 1)
                for j, cj in enumerate(LU):
                    LUfull[1 << j] = cj
                P5 = [1]
                for _ in range(5):
                    P5 = gf.poly_mul(F, P5, LUfull)
                diff = [a ^ b for a, b in zip(P5, ZS)]
                assert gf.deg(diff) <= n // 2
                agree = sum(1 for x in D if gf.poly_eval(F, diff, x) == gf.poly_eval(F, P5, x))
                assert agree == 5 * n // 8
                # genuine variant through a point p of S
                pt = D[min(S)]
                cst = gf.poly_eval(F, P5, pt)
                # (P_S - P_S(pt)) / (X - pt) has degree < n/2 : P_S(pt) = L_U^5(pt) since pt in S
                assert gf.poly_eval(F, diff, pt) == cst
                assert gf.deg(diff) - 1 < n // 2
            print(f"   {name}: full-degree check on 3 members: deg(L_U^5 - Z_S) <= n/2, agreement exactly 5n/8, punctured degree < n/2")


def half_tables(F, pts, t):
    """All subsets of pts: dict (size, e_1..e_t) -> count."""
    tab = {}
    m = len(pts)
    e = [[1] + [0] * t]

    def rec(i, cur, size):
        if i == m:
            key = (size,) + tuple(cur[1:])
            tab[key] = tab.get(key, 0) + 1
            return
        rec(i + 1, cur, size)
        s = pts[i]
        nxt = cur[:]
        for j in range(t, 0, -1):
            if cur[j - 1]:
                nxt[j] ^= F.mul(s, cur[j - 1])
        rec(i + 1, nxt, size + 1)

    rec(0, e[0], 0)
    return tab


def count_class(F, D, T, target, t):
    """Number of T-subsets S of D with (e_1..e_t)(S) = target, meet in the middle."""
    h = len(D) // 2
    A, B = D[:h], D[h:]
    tb = half_tables(F, B, t)
    cnt = 0
    e = [1] + [0] * t

    def rec(i, cur, size):
        nonlocal cnt
        if i == h:
            # need e(B) with sum_{a+b=j} eA_a eB_b = target_j
            eb = [1]
            for j in range(1, t + 1):
                v = target[j - 1]
                for a in range(1, j + 1):
                    if cur[a] and eb[j - a]:
                        v ^= F.mul(cur[a], eb[j - a])
                eb.append(v)
            cnt += tb.get((T - size,) + tuple(eb[1:]), 0)
            return
        rec(i + 1, cur, size)
        s = A[i]
        nxt = cur[:]
        for j in range(t, 0, -1):
            if cur[j - 1]:
                nxt[j] ^= F.mul(s, cur[j - 1])
        rec(i + 1, nxt, size + 1)

    rec(0, e, 0)
    return cnt


def check_mitm():
    rng = random.Random(32)
    N, n = 5, 32
    for name, basis in (("leanVM shape span(1..x^4) in K", gf.power_basis(N)), ("random basis in K", gf.random_basis(F, N, rng)),
                        ("second random basis in K", gf.random_basis(F, N, rng))):
        D = gf.span(basis)
        # U = span of the first two basis vectors (4 points), cosets labelled by the top 3 bits
        S58 = [i for i in range(n) if (i >> 2) in (0, 1, 2, 3, 4)]  # five cosets of U: a member of the 5n/8 class
        e = gf.top_coeffs(F, [D[i] for i in S58], 4)
        c3 = count_class(F, D, 20, e[1:4], 3)  # degree <= n/2: share e_1..e_3
        c4 = count_class(F, D, 20, e[1:5], 4)  # genuine: share e_1..e_4
        # punctured word: 19-sets S with (X - p) Z_S sharing e_1..e_3 with the class, p = D[0] = 0 in S58
        # with p = 0 the factor (X - 0) does not change e_j, so count 19-sets with the same e_1..e_3
        c19 = count_class(F, D, 19, e[1:4], 3)
        # 9n/16: seven cosets of Y (2 points): complement has 18 points; genuine codewords need e_1, e_2 (depth n/16 = 2)
        S7 = [i for i in range(n) if (i >> 1) in range(7)]
        S18 = [i for i in range(n) if i not in S7]
        e18 = gf.top_coeffs(F, [D[i] for i in S18], 3)
        c18_2 = count_class(F, D, 18, e18[1:3], 2)
        c18_3 = count_class(F, D, 18, e18[1:4], 3)
        print(f"n=32, {name}: class of the word L_U^5 at T=20: {c3} sets in degree <= 16, {c4} in degree < 16; "
              f"punctured word at T=19, degree < 16: {c19}; class of 18-sets (complement of seven cosets): {c18_2} at depth 2, {c18_3} at depth 3")


def check_extra():
    rng = random.Random(916)
    # (i) note 05 Proposition 3.1 at rate 1/2, b = 2: P (3n/16 points in one coset of a codimension-2 subspace Y) plus one
    # affine hyperplane F_i in each of the three other cosets: 9n/16 points, common top L_P X^(3n/8) with gap n/16.
    for N in (6, 7):
        n = 1 << N
        D = gf.span(gf.power_basis(N))
        cos = [[x for x in range(n) if x >> (N - 2) == c] for c in range(4)]  # cosets of Y = bottom N-2 bits
        P = rng.sample(cos[3], 3 * n // 16)
        tops = set()
        t = n // 16
        for _ in range(40):
            S = list(P)
            for c in range(3):
                while True:
                    phi = rng.randrange(1, 1 << (N - 2))  # a functional on Y: the hyperplane is not the whole coset
                    break
                bit = rng.randrange(2)
                S += [x for x in cos[c] if (bin(x & phi).count("1") & 1) == bit]
            assert len(S) == 9 * n // 16
            e = gf.top_coeffs(F, [D[i] for i in S], t)
            tops.add(tuple(e[1:t]))
        assert len(tops) == 1
        per = 2 * ((1 << (N - 2)) - 1)
        print(f"stack at 9n/16, N={N}: 40 random members share e_1..e_(n/16-1) (degree of differences <= n/2); "
              f"count per padding = (2^(N-1) - 2)^3 = {per ** 3}")
    print(f"   at N=25: (2^24 - 2)^3 = 2^{3 * 24:.0f} members in degree <= n/2 at agreement 9n/16")
    # (ii) note 02 Theorem 5 with M' = 16, g = 9: nu = number of 18-subsets of F_2^5 with a given nonzero sum
    cnt = {(0, 0): 1}
    for x in range(32):
        new = dict(cnt)
        for (c, v), w in cnt.items():
            if c < 18:
                new[(c + 1, v ^ x)] = new.get((c + 1, v ^ x), 0) + w
        cnt = new
    nu = cnt[(18, 1)]
    assert nu == 14732720 and comb(16, 9) == 11440
    import math
    tot25 = comb(16, 9) + ((1 << 21) - 1) * (nu - comb(16, 9))
    print(f"glued unions at 9n/16: nu = {nu}; members at N=25: {tot25} = 2^{math.log2(tot25):.2f}")
    # one sampled field check at N = 7: U of size n/16 = 8, W hyperplane of U (4 points), 18 of 32 labels with sum eta
    N, n = 7, 128
    D = gf.span(gf.power_basis(N))
    tops = set()
    for trial in range(30):
        # U = bottom 3 bits; W = kernel of a random nonzero functional on U
        phi = rng.randrange(1, 8)
        W = [u for u in range(8) if bin(u & phi).count("1") % 2 == 0]
        eta_lab = min(u for u in range(8) if u not in W)  # label of U \ W
        lab = lambda x: min(x ^ w for w in W)
        labs = sorted({lab(x) for x in range(n)})
        while True:
            Y = rng.sample(labs, 17)
            sx = 0
            for y in Y:
                sx ^= y
            last = lab(sx ^ eta_lab)
            if last not in Y:
                Y.append(last)
                break
        Ys = set(Y)
        S = [x for x in range(n) if lab(x) in Ys]
        assert len(S) == 72
        e = gf.top_coeffs(F, [D[i] for i in S], n // 16)
        tops.add(tuple(e[1:n // 16]))
    assert len(tops) == 1
    print("   N=7: 30 random glued members (varying hyperplane of U) share e_1..e_(n/16-1): differences of degree <= n/2 at agreement 9n/16")
    # (iii) note 01, 3.4 with a random B of density 1/4 on a 14-dimensional quotient
    M = 1 << 14
    w = [0] * M
    for i in rng.sample(range(M), M // 4):
        w[i] = 1
    h = 1
    while h < M:
        for i in range(0, M, 2 * h):
            for j in range(i, i + h):
                a, b = w[j], w[j + h]
                w[j], w[j + h] = a + b, a - b
        h *= 2
    vals = sorted((abs(v) for v in w[1:]), reverse=True)
    v1024 = vals[1023]
    print(f"random padding B (|B| = n/4, 14-dimensional quotient): the 1024-th largest |hat B| is {v1024}: 2^10 polynomials of degree <= n/2 "
          f"at agreement >= {0.625 + v1024 / (2 * M):.4f} n; top value {vals[0]} ({0.625 + vals[0] / (2 * M):.4f} n)")
    # (iv) rate 1/4 at 3n/8 by complements (note 05, Corollary 2.3), N = 6
    N, n = 6, 64
    Ub = [1, 2, 4]
    famA, famB, _, _ = five8_family(N, Ub)
    D = gf.span(gf.power_basis(N))
    tops = set()
    for S in rng.sample(list(famA), 300):
        comp = [x for x in range(n) if x not in S]
        e = gf.top_coeffs(F, [D[i] for i in comp], n // 8)
        tops.add(tuple(e[1:n // 8]))
    assert len(tops) == 1
    print(f"rate 1/4 at 3n/8, N=6: 300 complements of members of the 5n/8 class share e_1..e_(n/8-1): differences of degree <= n/4")


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    if what in ("flats", "all"):
        check_flats()
    if what in ("thmw", "all"):
        check_thmw()
    if what in ("five8", "all"):
        check_five8(int(sys.argv[2]) if len(sys.argv) > 2 else 6)
    if what in ("mitm", "all"):
        check_mitm()
    if what in ("extra", "all"):
        check_extra()
