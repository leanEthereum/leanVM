"""Note 77, Theorem 5.2: an aligned pattern has exactly the lifted relations.
For a subspace D (kind P or random), a subspace V of D (m = |V|), a random top pattern on D' = W_V(D) and a common exceptional set G
of g < m points inside one block that lies in every class: rel = (m - g) rel'_{<n'-k'} + g rel'_{<n'-k'-1}, where rel = weight - rank,
rel'_{<n'-k'} is weight' - rank' for RS_{k'}(D') and rel'_{<n'-k'-1} is weight' - rank' for RS_{k'+1}(D'). With g = 0: s = m s'."""
import random, importlib.util, os
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "74_gfpy.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
mul = gf.mul
def span(b):
    p = [0]
    for t in b: p += [q ^ t for q in p]
    return p
def inc_rank(points, k, classes, L):
    """classes[i]: tuple of members (subset of 0..L) agreeing at points[i]; returns (weight, rank)"""
    rows = []; w = 0
    for y, cl in zip(points, classes):
        if len(cl) < 2: continue
        pw = [1]
        for _ in range(k - 1): pw.append(mul(pw[-1], y))
        l0 = min(cl)
        for l in cl:
            if l == l0: continue
            row = [0] * (L * k)
            row[(l - 1) * k:(l - 1) * k + k] = pw
            if l0 >= 1: row[(l0 - 1) * k:(l0 - 1) * k + k] = pw
            rows.append(row); w += 1
    return w, (gf.rank(rows) if rows else 0)
rnd = random.Random(5)
bad = 0; tot = 0; nontrivial = 0
for trial in range(400):
    N = rnd.choice([4, 5]); kind = rnd.choice("PG")
    basis = [1 << i for i in range(N)] if kind == "P" else [rnd.getrandbits(64) for _ in range(N)]
    D = span(basis)
    if len(set(D)) != len(D): continue
    j = rnd.choice([1, 2]); m = 1 << j
    # V: a random j-dimensional subspace of D (not in the flag in general)
    while True:
        vb = [rnd.choice(D[1:]) for _ in range(j)]
        V = span(vb)
        if len(set(V)) == m: break
    W = lambda y: gf_prod([y ^ v for v in V])
    def gf_prod(xs):
        r = 1
        for t in xs: r = mul(r, t)
        return r
    blocks = {}
    for y in D: blocks.setdefault(W(y), []).append(y)
    Dp = list(blocks); n1 = len(Dp); r = rnd.choice([1, 2]); k1 = max(1, n1 >> r); k = m * k1
    L = rnd.choice([2, 3])
    def rand_class():
        if rnd.random() < 0.3: return ()
        cl = tuple(l for l in range(L + 1) if rnd.random() < 0.55)
        return cl if len(cl) >= 2 else ()
    top = [rand_class() for _ in Dp]
    g = rnd.choice([0, 0, 1, m - 1])
    if g:
        q0 = rnd.randrange(n1); top[q0] = tuple(range(L + 1)); G = set(rnd.sample(blocks[Dp[q0]], g))
    else: G = set()
    pts = []; cls = []
    for q, t in zip(Dp, top):
        for y in blocks[q]: pts.append(y); cls.append(() if y in G else t)
    w, rk = inc_rank(pts, k, cls, L)
    w1, rk1 = inc_rank(Dp, k1, top, L)
    if k1 + 1 <= n1: w1b, rk1b = inc_rank(Dp, k1 + 1, top, L)
    else: w1b, rk1b = w1, w1  # degree bound 0: no relation
    pred = (m - g) * (w1 - rk1) + g * (w1b - rk1b)
    tot += 1; bad += (w - rk != pred); nontrivial += (w - rk > 0)
print(f"Theorem 5.2: {tot} random aligned patterns (N = 4, 5; |V| = 2, 4; 3 and 4 members; kinds P and G; g = 0, 1, m-1): relation count differs from the prediction in {bad}; patterns with at least one relation: {nontrivial}")
