# Lead, note 68 Section 26. Best agreement threshold a union bound over agreement patterns can give
# over a field of B usable bits per independent event, for lists of fewer than M members.
#   per leaf:      a pattern at tau_gen + eps has eps*n independent events (one per surplus leaf)
#   per incidence: it has M*eps*n independent events (one per surplus row); the count of a random linear code
# tau_gen(M): smallest agreement at which no list of M members exists generically.
#   ideal:  (1 + (M-1) rho) / M (higher order MDS)
#   lifted: lower bounds from the lifted lists of note 69 (tree codes and Reed-Solomon on a subspace)
import math
def h(x): return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)
def solve(tg, M, B, per_leaf):
    # smallest tau >= tg with tau - tg >= (entropy of the patterns) / (bits of the events), by scanning
    c = M / B if per_leaf else 1.0 / B
    t = tg
    while t < 1.0:
        if t - tg >= c * h(t): return t
        t += 1e-4
    return 1.0
LIFT = {0.5: {3: 0.746, 4: 0.695, 5: 0.672, 6: 0.652, 7: 0.645, 8: 0.637},
        0.25: {3: 0.539, 4: 0.496, 5: 0.465, 6: 0.445, 7: 0.422, 8: 0.410}}
for rho in (0.5, 0.25):
    print(f"rate {rho}: Johnson {math.sqrt(rho):.4f}")
    for B in (62, 126):
        for name, per_leaf in (("per leaf", True), ("per incidence", False)):
            ideal = min((solve((1 + (M - 1) * rho) / M, M, B, per_leaf), M) for M in range(2, 200))
            lift = min((solve(t, M, B, per_leaf), M) for M, t in LIFT[rho].items())
            q = lambda t: math.ceil(108 / math.log2(1 / t))
            print(f"  {B} bits, {name:13s}: ideal code {ideal[0]:.4f} (M = {ideal[1]}, {q(ideal[0])} queries);"
                  f" with lifted lists {lift[0]:.4f} (M = {lift[1]}, {q(lift[0])} queries)")
    print(f"  queries at Johnson: {math.ceil(108 / math.log2(1 / math.sqrt(rho)))}")
