#!/usr/bin/env python3
"""Note 62 toy checks, part 2. Usage: python3 62_toy2.py lattice | tr | all

lattice : Lemma 5.4. Random window systems and configurations over GF(16), n = 12:
          dim{v in (K[X]_{<j})^2 : type-1 conditions} = (j-e1)_+ + (j-e2)_+ for all j,
          e1 + e2 = |Y1|, and the full count with type-2 points for degree < k.
tr      : Proposition T, by brute force over all pairs (d1, d2): GF(8), n = 8, k = 3,
          random 1-out windows (2 points), pattern U3 = D. For every T the exact value of
          E_T = sum over independent d of prod_{x in T} (q^Delta_x(d) - 1) = sum over
          configurations with support T of N, against q^(2k + 2|T| - |N[T]|).
"""
import itertools, math, random, sys, importlib.util, os

_d = os.path.dirname(os.path.abspath(__file__))
_s = importlib.util.spec_from_file_location("gf62", os.path.join(_d, "62_gf.py"))
gf = importlib.util.module_from_spec(_s)
_s.loader.exec_module(gf)


def cond_rows(F, conds, j):
    """rows of the conditions lam . (v1(y), v2(y)) = 0 on pairs of degree < j."""
    rows = []
    for y, lam in conds:
        pw, p = [], 1
        for _ in range(j):
            pw.append(p)
            p = F.mul(p, y)
        rows.append([F.mul(lam[0], t) for t in pw] + [F.mul(lam[1], t) for t in pw])
    return rows


def test_lattice(rng, trials=300):
    F = gf.GF(4)
    pts = rng.sample(range(F.q), 12)
    bad = 0
    stats = {"transversal": 0, "non-transversal": 0}
    for _ in range(trials):
        d = rng.choice([2, 3])
        windows = {x: [x] + rng.sample([y for y in pts if y != x], d) for x in pts}
        T = rng.sample(pts, rng.randrange(1, 7))
        dirs = [(1, 0), (0, 1), (1, 1), (1, rng.randrange(2, F.q))]
        sig = {x: rng.choice(dirs[: rng.choice([1, 2, 4])]) for x in T}
        lam = {}
        for x in T:
            for y in windows[x]:
                lam.setdefault(y, set()).add(sig[x])
        Y1 = [(y, next(iter(s))) for y, s in lam.items() if len(s) == 1]
        Y2 = [y for y, s in lam.items() if len(s) > 1]
        dims = []
        for j in range(0, len(Y1) + 3):
            rk = F.rank(cond_rows(F, Y1, j)) if (Y1 and j) else 0
            dims.append(2 * j - rk)
        e1 = next(j for j in range(len(dims)) if j + 1 < len(dims) and dims[j + 1] >= 1) if Y1 else 0
        e2 = len(Y1) - e1
        ok = e1 <= e2 and all(dims[j] == max(j - e1, 0) + max(j - e2, 0) for j in range(len(dims)))
        for k in (3, 5, 7):
            full = cond_rows(F, Y1, k) + cond_rows(F, [(y, (1, 0)) for y in Y2] + [(y, (0, 1)) for y in Y2], k)
            dim = 2 * k - (F.rank(full) if full else 0)
            kp = k - len(Y2)
            ok &= dim == max(kp - e1, 0) + max(kp - e2, 0)
            stats["transversal" if e2 <= kp else "non-transversal"] += 1
        bad += not ok
    print("lattice: Lemma 5.4 on %d random configurations (GF(16), n = 12, k = 3, 5, 7): %s; cases %s"
          % (trials, "OK" if bad == 0 else "FAIL (%d)" % bad, stats))


def test_tr(rng):
    F = gf.GF(3)
    q, n, k = F.q, 8, 3
    pts = list(range(q))
    windows = [[x] + rng.sample([y for y in pts if y != x], 1) for x in pts]
    polys = list(itertools.product(range(q), repeat=k))
    ev = [[F.ev(p, y) for y in pts] for p in polys]
    mul = F.mul
    E = {}
    for pa, a in zip(polys, ev):
        for pb, b in zip(polys, ev):
            if all(mul(pa[i], pb[j]) == mul(pa[j], pb[i]) for i in range(k) for j in range(i)):
                continue  # linearly dependent pair
            fac = []
            for x in pts:
                w = windows[x]
                v = [(a[y], b[y]) for y in w]
                if all(s == 0 and t == 0 for s, t in v):
                    fac.append((x, q * q - 1))
                elif all(mul(v[i][0], v[j][1]) == mul(v[j][0], v[i][1]) for i in range(len(w)) for j in range(i)):
                    fac.append((x, q - 1))
            for r in range(len(fac) + 1):
                for sub in itertools.combinations(fac, r):
                    key = frozenset(x for x, _ in sub)
                    pr = 1
                    for _, f in sub:
                        pr *= f
                    E[key] = E.get(key, 0) + pr
    worst = {}
    for T, val in E.items():
        NT = set()
        for x in T:
            NT |= set(windows[x])
        excess = math.log(val, q) - (2 * k + 2 * len(T) - len(NT))
        key = "|N[T]| <= k" if len(NT) <= k else "|N[T]| > k"
        if key not in worst or excess > worst[key][0]:
            worst[key] = (excess, sorted(T), len(NT))
    tot = math.log(sum(E.values()), q)
    print("tr: GF(8), n = 8, k = 3, windows of 2 points; log_q E_T - (2k + 2|T| - |N[T]|), worst cases:")
    for key, (ex, T, nt) in sorted(worst.items()):
        print("   %-12s max excess %+.3f at T = %s, |N[T]| = %d" % (key, ex, T, nt))
    print("   log_q sum over independent d of q^loss(d) = %.3f against 2k = %d (pattern U3 = D)" % (tot, 2 * k))


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    rng = random.Random(62)
    if mode in ("lattice", "all"):
        test_lattice(rng)
    if mode in ("tr", "all"):
        test_tr(rng)
