"""Note 64, item 2: a plain Reed-Solomon triple on the quotient D/W lifts to the mixed code with the local window
C = {0, b_0, b_1} (W = span(b_0, b_1)) with all agreements free, and does not lift with the cube window.

N = 6, GF(2^8). Quotient domain D' = L_W(D), 16 points, degree < k' = k/4. The triple is 0, g*f_1, g*f_2 with g the
vanishing polynomial of c common zeros, f_1 and f_2 fully split on D', and f_1 + lam*f_2 with many roots in D' (found
by random search over root sets). Counted: u_2 + 2 u_3 for the best word, against 2k.
"""
import importlib.util, random, sys, os

spec = importlib.util.spec_from_file_location("lib64", os.path.join(os.path.dirname(__file__), "64_lib.py"))
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)
rng = random.Random(642)
F, N = L.GF(8), 6
n = 1 << N


def peval(p, x):
    s = 0
    for c in reversed(p):
        s = F.mul(s, x) ^ c
    return s


def compose(Q, LW):
    out = [0]
    for c in reversed(Q):
        out = L.poly_mul(F, out, LW)
        out[0] ^= c
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def count3(s1, s2):
    """u_2 + 2 u_3 for the triple of symbol vectors (0, s1, s2), best word."""
    return sum(2 if (a == 0 and b == 0) else (1 if (a == 0 or b == 0 or a == b) else 0) for a, b in zip(s1, s2))


def find_quotient_triple(Dq, kq, c, target):
    """Search g, f1, f2 on the quotient with pointwise count >= target. Returns (Q1, Q2, count)."""
    deg = kq - 1 - c
    while True:
        pts = Dq[:]
        rng.shuffle(pts)
        G, A, B, rest = pts[:c], pts[c:c + deg], pts[c + deg:c + 2 * deg], pts[c + 2 * deg:]
        f1, f2 = L.vanishing(F, A), L.vanishing(F, B)
        lam = {}
        for x in rest:
            lam.setdefault(F.mul(peval(f1, x), F.inv(peval(f2, x))), []).append(x)
        best = max(lam.items(), key=lambda t: len(t[1]))
        cnt = 2 * c + 2 * deg + len(best[1])
        if cnt >= target:
            g = L.vanishing(F, G)
            return L.poly_mul(F, g, f1), L.poly_mul(F, g, [F.mul(best[0], a) for a in f2]), cnt


def run(k, c, target):
    kq = k // 4
    LW = L.vanishing(F, [0, 1, 2, 3])
    Dq = sorted({peval(LW, v) for v in range(n)})
    assert len(Dq) == n // 4
    Q1, Q2, cq = find_quotient_triple(Dq, kq, c, target)
    assert len(Q1) <= kq and len(Q2) <= kq
    P1, P2 = compose(Q1, LW), compose(Q2, LW)
    assert len(P1) <= k and len(P2) <= k
    pw = L.powers(F, n, k)
    e1 = L.evaluate(F, pw, P1 + [0] * (k - len(P1)))
    e2 = L.evaluate(F, pw, P2 + [0] * (k - len(P2)))
    e12 = [a ^ b for a, b in zip(e1, e2)]
    print(f"k={k} (k'={kq}, 2k'={2*kq}): quotient triple with u_2+2u_3 = {cq}; plain RS on D: {count3(e1, e2)}; 2k = {2*k}")
    for name, dirs in (("local window {0,b0,b1}", [0, 1]), ("cube window", list(range(N)))):
        free = [len(L.interior([v for v in range(n) if e[v] == 0], N, dirs)) for e in (e1, e2, e12)]
        res = []
        for _ in range(20):
            mu = L.sample_mu(F, n, len(dirs) + 1, rng)
            res.append(count3(L.mix(F, mu, e1, dirs), L.mix(F, mu, e2, dirs)))
        print(f"   {name}: free pair agreements {free}; u_2+2u_3 over 20 mu: min {min(res)} mean {sum(res)/20:.2f}"
              f" max {max(res)}; random-agreement prediction 3n/q = {3*n/F.q:.2f}")


if __name__ == "__main__":
    run(16, 0, 9)    # rate 1/4: three disjoint fibres of 3 points on the quotient, 9 > 2k' = 8
    run(32, 3, 17)   # rate 1/2: 3 common zeros, fibres 4, 4, 3: 17 > 2k' = 16
    run(32, 3, 18)   # rate 1/2: 3 common zeros, fibres 4, 4, 4: 18 > 2k' = 16
