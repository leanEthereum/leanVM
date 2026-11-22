# 30_validate: Lemma 4.1 of note 30 (rank is lower semicontinuous under merges and half-restrictions) on random
# three-set patterns, half of them periodic. A dependent pattern must have only dependent merges and restrictions.
#   python3 30_validate.py        (about two minutes)
import sys, random, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from importlib import import_module
L = import_module('30_lib')
rng = random.Random(7)
P = {d: L.subspace(d, rng) for d in range(5)}
# semicontinuity check at N = 3 and 4: singular patterns must have all merges and all restrictions singular
def check(N, delta, trials):
    n = 1 << N; K = delta + 1
    stats = dict(sing=0, nons=0, viol=0, res_ok=0, merge_ok=0)
    for _ in range(trials):
        # random pattern, biased to periodic ones half the time
        perm = list(range(n)); rng.shuffle(perm)
        while True:
            r0 = rng.randint(1, delta); r1 = rng.randint(1, delta); r2 = 2 * delta + 2 - r0 - r1
            if 0 <= r2 <= delta and r0 + r1 + r2 <= n: break
        if rng.random() < 0.5:
            idx = perm
        else:
            a = rng.randrange(1, n); cl = {}
            for p in range(n): cl.setdefault(min(p, p ^ a), []).append(p)
            cls = list(cl.values()); rng.shuffle(cls); idx = [p for c in cls for p in c]
        ms = [[0] * n for _ in range(3)]
        for j, p in enumerate(idx[:r0 + r1 + r2]):
            ms[0 if j < r0 else 1 if j < r0 + r1 else 2][p] = 1
        sing = len(L.pattern_kernel(P[N], ms, K)[0]) > 0
        mg = any(len(L.pattern_kernel(P[N - 1], [L.push(m, a) for m in ms], K)[0]) == 0 for a in range(1, n))
        rs = False
        for f in range(1, n):
            for c in range(2):
                q = [L.restrict(m, f, c) for m in ms]
                if min(x[1] for x in q) == 0 and len(L.pattern_kernel(P[N - 1], [x[0] for x in q], K, infs=[x[1] for x in q])[0]) == 0:
                    rs = True
        stats['sing' if sing else 'nons'] += 1
        if sing and (mg or rs): stats['viol'] += 1
        if not sing: stats['res_ok'] += rs; stats['merge_ok'] += mg
    print(N, delta, stats)
check(3, 2, 300); check(3, 3, 200); check(4, 4, 200); check(4, 6, 150)
