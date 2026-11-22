#!/usr/bin/env python3
"""Researcher 15: completeness of point batches introduced in the middle of a level (Protocol D with a schedule).

GF(2^8), a level with ell fold rounds and 2^ell lanes of degree < 2^kappa (no high part at the start, as for an honest
commitment; the folds grow by one coefficient a round). A batch sampled before round b is answered on the tuple after
b - 1 rounds, y = ev^(b-1)_z(P^(b-1)) = sum_u theta^(e_(b-1)(u)) P_u(zeta), e_j(u) = sum_{k > j} (1 - u_k) 2^(k-1), and
carried by v <- v + (theta^(2^(j-1)) + alpha_j + beta_j zeta) phi_j with phi_j = ev^(j)_z(F^(j)), for j = b .. ell.
Checked: at the end of the level v = P^(ell)(zeta) for every point of every batch (the identity the verifier's
conversion to the next level relies on), and a wrong answer or a wrong phi breaks it.

Usage: python3 15_batch_toy.py [seed]
"""
import random
import sys

M = 8
POLY = 0x11B
Q = 1 << M


def mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        if a >> M:
            a ^= POLY
        b >>= 1
    return r


def gpow(a, e):
    r = 1
    while e:
        if e & 1:
            r = mul(r, a)
        a = mul(a, a)
        e >>= 1
    return r


def peval(co, x):
    r = 0
    for c in reversed(co):
        r = mul(r, x) ^ c
    return r


def ev(tup, j, ell, theta, zeta):
    """ev^(j)_z of a tuple indexed by (u_{j+1}, .., u_ell); lane index: bit k - j - 1 is u_k."""
    r = 0
    for idx, lane in enumerate(tup):
        e = 0
        for k in range(j + 1, ell + 1):
            u = (idx >> (k - j - 1)) & 1
            e += (1 - u) << (k - 1)
        r ^= mul(gpow(theta, e), peval(lane, zeta))
    return r


def halves(tup):
    """F = lanes with the next variable 0, G = lanes with it 1 (the next variable is the lowest index bit)."""
    return tup[0::2], tup[1::2]


def fold(tup, alpha, beta):
    F, G = halves(tup)
    out = []
    for f, g in zip(F, G):
        n = max(len(f) + 1, len(g))
        p = [0] * n
        for i, c in enumerate(g):
            p[i] ^= c
        for i, c in enumerate(f):
            p[i] ^= mul(alpha, c)
            p[i + 1] ^= mul(beta, c)
        out.append(p)
    return out


def run(rng, ell, kappa, schedule, tamper=None):
    tup = [[rng.randrange(Q) for _ in range(1 << kappa)] for _ in range(1 << ell)]
    pts = []  # [theta, zeta, v, batch]
    ok = True
    for j in range(1, ell + 1):
        for _ in range(schedule.get(j, 0)):
            theta, zeta = rng.randrange(Q), rng.randrange(Q)
            y = ev(tup, j - 1, ell, theta, zeta)
            if tamper == ("answer", j):
                y ^= 1
            pts.append([theta, zeta, y, j])
        F, G = halves(tup)
        phis = [ev(F, j, ell, p[0], p[1]) for p in pts]
        if tamper == ("phi", j) and phis:
            phis[0] ^= 1
        alpha, beta = rng.randrange(Q), rng.randrange(Q)
        for p, phi in zip(pts, phis):
            p[2] ^= mul(gpow(p[0], 1 << (j - 1)) ^ alpha ^ mul(beta, p[1]), phi)
        tup = fold(tup, alpha, beta)
        # the carried value is the round-j evaluation of the folded tuple (E2 + E3 of Lemma D1)
        for p in pts:
            if p[2] != ev(tup, j, ell, p[0], p[1]):
                ok = False
    assert len(tup) == 1
    for p in pts:
        if p[2] != peval(tup[0], p[1]):
            ok = False
    return ok, len(pts)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    runs = ids = 0
    for ell, kappa in ((3, 3), (4, 2), (6, 1)):
        for _ in range(20):
            schedule = {1: rng.randrange(1, 4)}
            for b in range(2, ell + 1):
                if rng.random() < 0.5:
                    schedule[b] = rng.randrange(1, 4)
            ok, n = run(rng, ell, kappa, schedule)
            assert ok, (ell, kappa, schedule)
            runs += 1
            ids += n * (ell + 1)
    print("honest runs: %d, identities checked: about %d, all hold" % (runs, ids))
    rej = tot = 0
    for ell, kappa in ((3, 3), (4, 2)):
        for b in range(1, ell + 1):
            for kind in ("answer", "phi"):
                for _ in range(10):
                    schedule = {1: 2, b: 2}
                    ok, _ = run(rng, ell, kappa, schedule, tamper=(kind, b))
                    tot += 1
                    rej += not ok
    print("altered runs (one answer or one phi of a batch changed): %d of %d break an identity" % (rej, tot))


if __name__ == "__main__":
    main()
