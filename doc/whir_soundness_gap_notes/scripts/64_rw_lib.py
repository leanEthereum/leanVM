"""Note 64, random windows (note 66): window tables, the mixed code c(P)(x) = P(x) + sum_l mu_l(x) P(pi_l(x)),
interiors, and a search for sets of at most s points with the largest interior."""
import random


def rand_windows(n, d, rng):
    """win[x] = [x, pi_1(x), .., pi_d(x)], partners distinct and different from x (axiom W1)."""
    return [[x] + rng.sample([y for y in range(n) if y != x], d) for x in range(n)]


def cube_windows(N):
    return [[x] + [x ^ (1 << i) for i in range(N)] for x in range(1 << N)]


def interior_w(Z, win):
    Z = set(Z)
    return [x for x in Z if all(y in Z for y in win[x])]


def mix_w(F, mu, ev, win):
    """mu[x] has d entries; the coefficient of P(x) itself is 1."""
    out = []
    for x, w in enumerate(win):
        s = ev[x]
        for c, y in zip(mu[x], w[1:]):
            s ^= F.mul(c, ev[y])
        out.append(s)
    return out


def best_interior(win, s, rng, restarts=60):
    """Largest T with |closure(T)| <= s found by randomized greedy plus swap local search.
    Returns (|T|, closure) ; closure(T) = union of the windows of T, a set Z with int(Z) containing T."""
    n = len(win)
    wset = [frozenset(w) for w in win]
    best = (0, set())
    for _ in range(restarts):
        T, Z = set(), set()
        while True:
            cands = []
            for x in range(n):
                if x not in T:
                    g = len(wset[x] - Z)
                    if len(Z) + g <= s:
                        cands.append((g + rng.random() * rng.choice((0.1, 1.5)), x))
            if not cands:
                break
            _, x = min(cands)
            T.add(x); Z |= wset[x]
        improved = True
        while improved:                      # swap one centre out, try to put two in
            improved = False
            for u in list(T):
                T2 = T - {u}
                Z2 = set().union(*[wset[x] for x in T2]) if T2 else set()
                add = []
                for x in sorted(range(n), key=lambda x: len(wset[x] - Z2) + rng.random()):
                    if x not in T2 and len(Z2 | wset[x]) <= s:
                        Z2 |= wset[x]; add.append(x)
                if len(add) >= 2:
                    T = T2 | set(add); Z = Z2; improved = True
                    break
        T = set(interior_w(Z, win))
        if len(T) > best[0]:
            best = (len(T), set(Z))
    return best
