"""Note 77, Theorem 3.4: over GF(2^64), Q_3 fails for EVERY Reed-Solomon code with k >= 65 and n >= 2k, on every evaluation set.
For a (k-1)-set A put f = Lambda_A. For S disjoint from A, |S| = k + 1, the k + 1 values phi(c) = f(c) * mu(c), c in S (mu the dual
codeword supported on S, mu(c) = 1/Lambda_S'(c)), are vectors of F_2^64, so a proper nonempty subset C of S has sum_C phi = 0, and then the
word (f on C, 0 on S \\ C) extends to a codeword g of degree < k: the three codewords 0, f, g coincide pairwise on A + S, 2k points.
Checked here at k = 128: n = 256 on D_8 = <1, x, .., x^7> (today's code), on a random subspace, and on 256 random points; and with slack
(|S| = k + 1 + s) at k = 128, n = 512."""
import random, importlib.util, os
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "74_gfpy.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
mul, inv = gf.mul, gf.inv
def prod(xs):
    r = 1
    for t in xs: r = mul(r, t)
    return r
def f2_dependency(vecs, want_proper=True):
    """vecs: list of (tuple of 64-bit ints); returns an index set C, nonempty and proper, with XOR of vecs over C = 0"""
    basis = {}  # pivot -> (vector as big int, index mask)
    out = []
    for i, v in enumerate(vecs):
        x = 0
        for part in v: x = (x << 64) | part
        m = 1 << i
        while x:
            p = x.bit_length()
            if p in basis: bx, bm = basis[p]; x ^= bx; m ^= bm
            else: basis[p] = (x, m); break
        if x == 0: out.append(m)
    return out
def lagrange_eval(xs, ys, y0):
    tot = 0
    for i, (xi, yi) in enumerate(zip(xs, ys)):
        if yi == 0: continue
        num = prod([y0 ^ xj for j, xj in enumerate(xs) if j != i]); den = prod([xi ^ xj for j, xj in enumerate(xs) if j != i])
        tot ^= mul(yi, mul(num, inv(den)))
    return tot
def run(name, D, k, s, rnd):
    A = rnd.sample(D, k - 1); rest = [d for d in D if d not in set(A)]
    S = rnd.sample(rest, k + 1 + s)
    fS = [prod([c ^ a for a in A]) for c in S]
    # dual codewords supported on S: mu_i(c) = c^i / Lambda_S'(c), i = 0..s
    dS = [inv(prod([c ^ c2 for c2 in S if c2 != c])) for c in S]
    vecs = []
    for j, c in enumerate(S):
        v = []; pw = dS[j]
        for i in range(s + 1): v.append(mul(pw, fS[j])); pw = mul(pw, c)
        vecs.append(tuple(v))
    deps = f2_dependency(vecs)
    full = (1 << len(S)) - 1
    cand = [m for m in deps if m != full]
    if len(cand) < 1 and len(deps) >= 2: cand = [deps[0] ^ deps[1]]
    m = cand[0]
    C = [j for j in range(len(S)) if (m >> j) & 1]
    # verification: interpolate g (degree < k) through k of the points of S, test the other s + 1
    ys = [fS[j] if (m >> j) & 1 else 0 for j in range(len(S))]
    ok = all(lagrange_eval(S[:k], ys[:k], S[j]) == ys[j] for j in range(k, len(S)))
    print(f"{name}: k={k} n={len(D)} slack s={s}: F_2-dependencies found {len(deps)} (>= {k + 1 + s - 64 * (s + 1)} predicted), |C|={len(C)}, |B|={len(S) - len(C)}, word extends to a codeword g: {ok}; coincidence points {k - 1 + len(S)} against Q_3's {2 * k - 1}")
rnd = random.Random(2026)
k = 128
run("today's code D_8", list(range(256)), k, 0, rnd)
def span(b):
    p = [0]
    for t in b: p += [q ^ t for q in p]
    return p
run("random subspace, dim 8", span([rnd.getrandbits(64) for _ in range(8)]), k, 0, rnd)
run("256 random points", list({rnd.getrandbits(64) for _ in range(256)}), k, 0, rnd)
run("today's code D_9, rate 1/4, slack 1", list(range(512)), k, 1, rnd)
run("512 random points, rate 1/4, slack 1", list({rnd.getrandbits(64) for _ in range(512)}), k, 1, rnd)
