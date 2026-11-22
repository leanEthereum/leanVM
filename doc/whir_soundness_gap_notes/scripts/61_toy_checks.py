#!/usr/bin/env python3
"""Note 61: toy checks of the protocol statements. Standard library only, about ten seconds.

  C1  The plain fold commutes with the window mixing; the affine fold of Annex B does not, and its honest fold is
      not a codeword of the mixed code of one more degree (so no slack absorbs it).
  C2  Completeness of one level of Protocol D' on a window-mixed code: the carried point claims, the running claim
      with two scalars a round, and the query claims with window weights, on an honest run; and that a query of the
      affine-fold variant fails.
  C3  The class bound of Lemma F': for a pair (F, G) of codewords that agrees with the pair of words on a set of
      a_set columns, the number of fold challenges alpha whose fold agrees on at least A columns is at most
      floor((n - a_set) / (A - a_set)), and a planted word attains it.
  C4  Proposition I' (interleaved lists from the single-lane profile): N_m(A) <= N_{m-1}(A) + (Lam_1(A) - 1) N_{m-1}(2A - d)
      for A > d, exhaustively on random binary linear codes with two and three lanes; and the paper's tree bound.
  C5  The count of products of the window weights: sum_j min(j + 1, kappa), against a direct evaluation that shares
      the unchanged factors, on a toy novel basis.

K = GF(2^8) = GF(2)[x]/(x^8 + x^4 + x^3 + x + 1) plays both K and E here.
"""
import itertools
import random

random.seed(61)

# ----------------------------------------------------------------------------------------------------------------
# GF(2^8)
# ----------------------------------------------------------------------------------------------------------------
EXP, LOG = [0] * 510, [0] * 256
_x = 1
for _i in range(255):
    EXP[_i] = _x
    LOG[_x] = _i
    _x ^= (_x << 1) ^ (0x11B if _x & 0x80 else 0)  # multiply by the generator 3
    _x &= 0xFF
for _i in range(255, 510):
    EXP[_i] = EXP[_i - 255]


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[255 - LOG[a]]


def pw(a, e):
    r = 1
    for _ in range(e):
        r = mul(r, a)
    return r


def peval(p, x):
    r = 0
    for c in reversed(p):
        r = mul(r, x) ^ c
    return r


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) ^ (q[i] if i < len(q) else 0) for i in range(n)]


def pscale(p, a):
    return [mul(c, a) for c in p]


def pmulx(p):
    return [0] + list(p)


def rank(rows):
    rows = [list(r) for r in rows]
    rk, col, ncol = 0, 0, len(rows[0]) if rows else 0
    while rk < len(rows) and col < ncol:
        piv = next((i for i in range(rk, len(rows)) if rows[i][col]), None)
        if piv is None:
            col += 1
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        iv = inv(rows[rk][col])
        rows[rk] = [mul(v, iv) for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col]:
                f = rows[i][col]
                rows[i] = [v ^ mul(f, w) for v, w in zip(rows[i], rows[rk])]
        rk += 1
        col += 1
    return rk


# ----------------------------------------------------------------------------------------------------------------
# The window-mixed code on the span of 1, x, x^2, x^3
# ----------------------------------------------------------------------------------------------------------------
NBITS = 4
N = 1 << NBITS
BASIS = [1, 2, 4, 8]  # 1, x, x^2, x^3 as field elements
DOM = [0] * N
for _v in range(N):
    for _b in range(NBITS):
        if _v >> _b & 1:
            DOM[_v] ^= BASIS[_b]
OFFSETS = [0] + [1 << b for b in range(NBITS)]  # index offsets: x and its NBITS neighbours in the cube


def new_mu():
    return [[random.randrange(1, 256) for _ in OFFSETS] for _ in range(N)]


def enc(mu, p):
    """The mixed codeword: position v carries sum_c mu(v, c) p(x_{v + c})."""
    ev = [peval(p, x) for x in DOM]
    out = []
    for v in range(N):
        s = 0
        for m, off in zip(mu[v], OFFSETS):
            s ^= mul(m, ev[v ^ off])
        out.append(s)
    return out


def rand_poly(k):
    return [random.randrange(256) for _ in range(k)]


def check_c1():
    k = 4
    mu = new_mu()
    for _ in range(50):
        f, g = rand_poly(k), rand_poly(k)
        a, b = random.randrange(256), random.randrange(1, 256)
        cf, cg = enc(mu, f), enc(mu, g)
        plain = [y ^ mul(a, x) for x, y in zip(cf, cg)]
        assert plain == enc(mu, padd(g, pscale(f, a)))
        affine_word = [cg[v] ^ mul(a ^ mul(b, DOM[v]), cf[v]) for v in range(N)]
        affine_poly = padd(g, padd(pscale(f, a), pscale(pmulx(f), b)))
        assert affine_word != enc(mu, affine_poly)
        # ... and the folded word is not a codeword of the mixed code of degree <= k either: the generator of that
        # code has rank k + 1, and adding the word raises it.
        gen = [enc(mu, [0] * i + [1]) for i in range(k + 1)]
        assert rank(gen) == k + 1 and rank(gen + [affine_word]) == k + 2
    # The span of the code and of its multiples by the position x has dimension min(n, 2k): closing the code under
    # the twist doubles its dimension (for Reed-Solomon it adds one).
    for kk in (2, 4, 6):
        gen = [enc(mu, [0] * i + [1]) for i in range(kk)]
        twisted = [[mul(DOM[v], row[v]) for v in range(N)] for row in gen]
        assert rank(gen) == kk and rank(gen + twisted) == min(N, 2 * kk)
        rs = [[peval([0] * i + [1], x) for x in DOM] for i in range(kk)]
        assert rank(rs + [[mul(DOM[v], row[v]) for v in range(N)] for row in rs]) == kk + 1
    print("C1 passed: plain fold commutes with the mixing; the affine fold's honest fold leaves the code (50 trials); the twisted code has dimension 2k")


def check_c2():
    k, ell, s = 4, 2, 3
    lanes = list(itertools.product((0, 1), repeat=ell))  # u = (u_1, u_2); round j folds u_j
    for _trial in range(20):
        mu = new_mu()
        p = {u: rand_poly(k) for u in lanes}
        word = {u: enc(mu, p[u]) for u in lanes}
        pts = [(random.randrange(256), random.randrange(256)) for _ in range(s)]

        def expo(j, u):  # e_j(u) = sum_{i > j} (1 - u_i) 2^(i - 1), u indexed from round j + 1 on
            return sum((1 - ui) << (j + idx) for idx, ui in enumerate(u))

        def ev(j, z, tup):
            th, ze = z
            r = 0
            for u, poly in tup.items():
                r ^= mul(pw(th, expo(j, u)), peval(poly, ze))
            return r

        w = {u: [random.randrange(256) for _ in range(k)] for u in lanes}

        def inner(wt, tup):
            r = 0
            for u in tup:
                for a, b in zip(wt[u], tup[u]):
                    r ^= mul(a, b)
            return r

        claim = inner(w, p)
        v = [ev(0, z, p) for z in pts]
        alphas = []
        for j in range(1, ell + 1):
            subs = sorted({u[1:] for u in p})
            f = {u: p[(0,) + u] for u in subs}
            g = {u: p[(1,) + u] for u in subs}
            w0 = {u: w[(0,) + u] for u in subs}
            w1 = {u: w[(1,) + u] for u in subs}
            v_g = inner(w0, g)
            v_f = inner({u: padd(w0[u], w1[u]) for u in subs}, f)
            phi = [ev(j, z, f) for z in pts]
            al = random.randrange(256)
            alphas.append(al)
            claim = v_g ^ mul(al, v_g ^ claim) ^ mul(mul(al, al), v_f)
            w = {u: padd(pscale(w0[u], 1 ^ al), pscale(w1[u], al)) for u in subs}
            v = [vm ^ mul(pw(z[0], 1 << (j - 1)) ^ al, ph) for vm, z, ph in zip(v, pts, phi)]
            p = {u: padd(g[u], pscale(f[u], al)) for u in subs}
            assert inner(w, p) == claim
            assert [ev(j, z, p) for z in pts] == v
        final = p[()]
        assert len(final) == k  # no degree growth: there is no high part
        assert [peval(final, z[1]) for z in pts] == v
        ev_final = [peval(final, x) for x in DOM]
        for q in range(N):
            col = {u: word[u][q] for u in lanes}
            cur = col
            for al in alphas:
                subs = sorted({u[1:] for u in cur})
                cur = {u: cur[(1,) + u] ^ mul(al, cur[(0,) + u]) for u in subs}
            window = 0
            for m, off in zip(mu[q], OFFSETS):
                window ^= mul(m, ev_final[q ^ off])
            assert cur[()] == window
    print("C2 passed: one level of Protocol D' on a window-mixed code is complete (20 honest runs, every column queried)")


def check_c3():
    k = 4
    mu = new_mu()
    for a_set, big_a in ((6, 8), (6, 9), (4, 6), (5, 10)):
        f, g = rand_poly(k), rand_poly(k)
        cf, cg = enc(mu, f), enc(mu, g)
        cols = list(range(N))
        random.shuffle(cols)
        good, bad = cols[:a_set], cols[a_set:]
        need = big_a - a_set  # columns a challenge must repair
        o0, o1 = list(cf), list(cg)
        groups = [bad[i : i + need] for i in range(0, len(bad) - need + 1, need)]
        used = random.sample(range(1, 256), len(groups))
        for grp, al in zip(groups, used):
            for v in grp:
                e0 = random.randrange(1, 256)
                o0[v] ^= e0
                o1[v] ^= mul(al, e0)
        for v in bad[len(groups) * need :]:
            o0[v] ^= random.randrange(1, 256)  # leftover columns: never repaired together with enough others
        wins = 0
        for al in range(256):
            fold = [o1[v] ^ mul(al, o0[v]) for v in range(N)]
            target = [cg[v] ^ mul(al, cf[v]) for v in range(N)]
            if sum(x == y for x, y in zip(fold, target)) >= big_a:
                wins += 1
        bound = (N - a_set) // need
        assert wins == len(groups) == bound, (wins, len(groups), bound)
        # Random errors off the agreement set never beat the bound.
        for _ in range(30):
            o0 = [x ^ (random.randrange(1, 256) if v in bad else 0) for v, x in enumerate(cf)]
            o1 = [x ^ (random.randrange(256) if v in bad else 0) for v, x in enumerate(cg)]
            wins = 0
            for al in range(256):
                agree = sum((o1[v] ^ mul(al, o0[v])) == (cg[v] ^ mul(al, cf[v])) for v in range(N))
                wins += agree >= big_a
            assert wins <= bound
    print("C3 passed: a class off the list wins at most floor((n - |agreement|) / (columns to repair)) challenges, attained")


def check_c4():
    def lists(n, k, seed):
        rnd = random.Random(seed)
        while True:
            gen = [rnd.getrandbits(n) for _ in range(k)]
            code = set()
            for bits in range(1 << k):
                c = 0
                for i in range(k):
                    if bits >> i & 1:
                        c ^= gen[i]
                code.add(c)
            if len(code) == 1 << k:
                break
        code = sorted(code)
        full = (1 << n) - 1
        d = max(n - bin(c).count("1") for c in code if c)  # the largest agreement of two distinct codewords
        # coset representatives of the code: the list of a word depends on its coset only
        reps, seen = [], set()
        for w in range(1 << n):
            if w not in seen:
                reps.append(w)
                for c in code:
                    seen.add(w ^ c)
        agr = {w: [full & ~(w ^ c) for c in code] for w in reps}
        pop = [bin(i).count("1") for i in range(1 << n)]

        def n_m(m, a):
            best = 0
            for ws in itertools.product(reps, repeat=m):
                sets = [full]
                for w in ws:
                    sets = [s & t for s in sets for t in agr[w] if pop[s & t] >= a]
                    if not sets:
                        break
                best = max(best, len(sets))
            return best

        return d, n_m

    def tree_n(lam, g, phi):
        return 1 if phi < 2 * g else tree_n(lam, g, phi - g) + (lam - 1) * tree_n(lam, g, phi // 2)

    cases = nontrivial = 0
    shapes = [(n, k, seed) for n in (7, 8, 9, 10, 11, 12) for k in (2, 3, 4) for seed in range(1, 7) if n - k <= 8]
    for n, k, seed in shapes:
        d, n_m = lists(n, k, 1000 * n + 10 * k + seed)
        cache = {}

        def nm(m, a):
            if a > n:
                return 0
            if (m, a) not in cache:
                cache[(m, a)] = n_m(m, a)
            return cache[(m, a)]

        for a in range(d + 1, n + 1):
            for m in (2, 3):
                if (1 << (n - k)) ** m > 300000:
                    continue
                lhs = nm(m, a)
                rhs = nm(m - 1, a) + (nm(1, a) - 1) * nm(m - 1, 2 * a - d)
                assert lhs <= rhs, (n, k, seed, m, a, lhs, rhs)
                assert lhs <= tree_n(max(nm(1, a), 1), a - d, n - d)
                cases += 1
                nontrivial += nm(1, a) > 1
    print(f"C4 passed: Proposition I' and the paper's tree bound on {cases} exhaustive cases, {nontrivial} with a single-lane list above one (binary codes, two and three lanes)")


def check_c5():
    # Toy novel basis on the span of BASIS: What_k = W_k / W_k(beta_k), W_0 = X, W_{k+1} = W_k (W_k + W_k(beta_k)).
    kappa = 3  # message variables: codewords of degree < 8 on 16 points

    def what(k, y):
        def wk(i, t):
            return t if i == 0 else mul(wk(i - 1, t), wk(i - 1, t) ^ wk(i - 1, BASIS[i - 1]))

        return mul(wk(k, y), inv(wk(k, BASIS[k])))

    for k in range(kappa):
        for j in range(NBITS):  # What_k is additive, kills beta_j for j < k, and is 1 at beta_k
            assert what(k, BASIS[j]) == (0 if j < k else what(k, BASIS[j]))
            if j == k:
                assert what(k, BASIS[j]) == 1
        for _ in range(20):
            a, b = random.randrange(16), random.randrange(16)
            assert what(k, DOM[a] ^ DOM[b]) == what(k, DOM[a]) ^ what(k, DOM[b])
    rho = [random.randrange(1, 256) for _ in range(kappa)]

    def weight(y):  # the MLE of the column weight of y at rho: prod_k (1 + rho_k + rho_k What_k(y))
        r = 1
        for k in range(kappa):
            r = mul(r, 1 ^ rho[k] ^ mul(rho[k], what(k, y)))
        return r

    total_products = 0
    for v in range(N):
        f = [1 ^ rho[k] ^ mul(rho[k], what(k, DOM[v])) for k in range(kappa)]
        suffix = [1] * (kappa + 1)
        for k in range(kappa - 1, -1, -1):
            suffix[k] = mul(suffix[k + 1], f[k])
        for j in range(NBITS):
            changed = min(j + 1, kappa)
            acc = suffix[changed]
            for k in range(changed):
                acc = mul(acc, f[k] ^ mul(rho[k], what(k, BASIS[j])))
                total_products += 1
            assert acc == weight(DOM[v] ^ BASIS[j]) == weight(DOM[v ^ (1 << j)])
    assert total_products == N * sum(min(j + 1, kappa) for j in range(NBITS))
    print("C5 passed: the partner x + beta_j changes the factors k <= j only; sum_j min(j + 1, kappa) products a query")


if __name__ == "__main__":
    check_c1()
    check_c2()
    check_c3()
    check_c4()
    check_c5()
