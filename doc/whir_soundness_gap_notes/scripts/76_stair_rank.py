"""Note 76: the 35-member one-sided staircase at (8,16) (blocks of 2 leaves, the zero of the lower factor at leaf 0).
Solution-space dimension by the duality of Proposition 4.1 of note 74: dim S = dim C^perp(S) - dim sum_l C^perp(S_l).
Then rank = Lk - dim S, to compare with the cell bound of Theorem 4.1 (at most 237)."""
import random, importlib.util, os, itertools
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
gf = load("74_gfpy"); du = load("76_dual")
rnd = random.Random(7676)
v = 3; n = 16; k = 8
tw = du.make_tw(v, 1, rnd)
G = [du.row(tw, v, j) for j in range(n)]
members = [S for S in itertools.combinations(range(1, 8), 4)]
duals = []
for S in members:
    leaves = [0] + [2 * q + b for q in S for b in (0, 1)]
    # dual codewords supported on the 9 leaves: y with sum_x y_x g_x = 0
    M = [[G[x][e] for x in leaves] for e in range(k)]
    ker = gf.kernel(M, len(leaves))
    assert len(ker) == 1
    y = [0] * n
    for i, x in enumerate(leaves): y[x] = ker[0][i]
    duals.append(y)
covered = sorted(set([0] + [2 * q + b for q in range(1, 8) for b in (0, 1)]))
r = gf.rank(duals)
dimS = (len(covered) - k) - r
L = len(members) - 1
w = sum(9 for _ in members) - len(covered)
print("members", len(members), "weight", w, "Lk", L * k, "rank of the span of the dual codewords", r, "dim S", dimS, "rank of the incidence system", L * k - dimS, "deficiency", w - (L * k - dimS))
