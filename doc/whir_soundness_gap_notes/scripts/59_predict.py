# 59_predict.py: first-moment prediction for 59_lists.c. For a uniformly random linear [16, k] code over GF(q)
# and linearly independent messages, the pairs (c1(x), c2(x)) are uniform and independent over the positions, so
# the expected number of ordered pairs (c1 up to scaling, c2) whose triple {0, c1, c2} reaches agreement >= T is exact.
import sys
from math import factorial


def best(z0, u1, u2, u3, n=16):
    b, r = 0, n - z0 - u1 - u2 - u3
    for v1 in range(u1 + 1):
        for v2 in range(u2 + 1):
            for v3 in range(u3 + 1):
                m = (z0 + u1 - v1 + u2 - v2 + v3, z0 + u1 - v1 + u3 - v3 + v2, z0 + u2 - v2 + u3 - v3 + v1)
                for a in range(n, b, -1):
                    if sum(max(0, a - x) for x in m) <= r:
                        b = a
                        break
    return b


q, n = int(sys.argv[1]) if len(sys.argv) > 1 else 16, 16
p0, p1, pr = 1 / q**2, (q - 1) / q**2, (q - 1) * (q - 2) / q**2
dist = [0.0] * (n + 1)
for z0 in range(n + 1):
    for u1 in range(n + 1 - z0):
        for u2 in range(n + 1 - z0 - u1):
            for u3 in range(n + 1 - z0 - u1 - u2):
                r = n - z0 - u1 - u2 - u3
                w = factorial(n) / (factorial(z0) * factorial(u1) * factorial(u2) * factorial(u3) * factorial(r))
                pr_ = w * p0**z0 * p1 ** (u1 + u2 + u3) * pr**r
                if pr_ > 1e-40:
                    dist[best(z0, u1, u2, u3)] += pr_
for k in (6, 8):
    pairs = (q**k - 1) / (q - 1) * (q**k - q)
    print(f"q={q} k={k}: expected ordered independent pairs with best agreement exactly A: " +
          " ".join(f"{a}:{pairs * dist[a]:.3g}" for a in range(9, 15)))
