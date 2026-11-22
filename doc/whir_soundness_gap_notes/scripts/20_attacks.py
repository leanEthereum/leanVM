#!/usr/bin/env python3
"""Referee check 2 (note 20): cheating provers against one fold round of Protocol D, counted exactly.

Standard library only. One lane per half (the last round of a level), so a point is its zeta and a constant
theta' = theta^(2^(j-1)). A candidate is a map challenge -> polynomial: the fold G_a + (alpha + beta X) F of a list
member (F, G_a), or a pole line. A challenge WINS for a prover message if some candidate satisfies every point
claim (p) and the running claim (w) of note 14, Lemma F:

  (p)  P(zeta_m) = v_m + (theta'_m + alpha + beta zeta_m) phi_m                      for every point m
  (w)  <(1+alpha) W_0 + alpha W_1, P> = v_G + alpha (v_G + sigma) + alpha^2 v_F + beta sigma_0 + alpha beta (sigma_0 + sigma_1)

with weights on the low part (coefficients below LOW). Winning challenges are counted by brute force over all q^2
challenges from these two definitions; where a maximum over prover messages is reported it is exact (all
q^5 messages (v_G, v_F, sigma_0, sigma_1, phi_i), through the restriction of (w) to the lines that (p) leaves, which
is cross-checked against the brute force on random messages).

Experiments (k members with one common first half F unless stated; "false claim" = sigma differs from every
member's value):

  X1  no point claims (today's round shape), false claim: k lines, about k q wins (note 03, Lemma 2)
  X2  s generic points answered for member 1, false claim: member 1's conic only
  X3  clique: all s points at roots of R, members U_1 + R H_a share every answer, false claim: about k q wins
  X4a note 16, Proposition 3.1: s-1 points at roots, one answer off, ZERO weight: exactly k q wins
  X4b the same with a random weight and a false claim: exact maximum over all messages. Two lines can always be
      aligned (four free values, two conditions a line), a third only at the degenerate point zeta = 0 (X4b')
  X4e members on one affine line, G_a = G + h_a Delta (note 16's own word has this shape), random weight, false
      claim for every member: all k lines can be aligned, k q wins (Proposition R3 of note 20)
  X4c members sharing their LOW part (they differ in the high part), claim TRUE for the common low part, one
      answer off: k q wins (an accepted run opens a true claim)
  X4d the same with a FALSE claim: exact maximum over all messages
  X5  N pole lines sharing every answer (all s points at roots), random weight: exact maximum over all messages,
      twelve instances

Usage: python3 20_attacks.py [seed]        (about two minutes on one idle thread)
"""
import random
import sys


class Field:
    def __init__(self, m, mod):
        self.m, self.q = m, 1 << m
        self.exp, self.log = [0] * (2 * self.q), [0] * self.q
        v = 1
        for i in range(self.q - 1):
            self.exp[i], self.log[v] = v, i
            v <<= 1
            if v >> m:
                v ^= mod
        assert v == 1 and len(set(self.exp[: self.q - 1])) == self.q - 1, "the modulus must be primitive"
        for i in range(self.q - 1, 2 * self.q):
            self.exp[i] = self.exp[i - (self.q - 1)]

    def mul(self, a, b):
        return 0 if a == 0 or b == 0 else self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[(self.q - 1 - self.log[a]) % (self.q - 1)]

    def ev(self, co, x):
        r = 0
        for c in reversed(co):
            r = self.mul(r, x) ^ c
        return r

    def pmul(self, a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    out[i + j] ^= self.mul(x, y)
        return out


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) ^ (b[i] if i < len(b) else 0) for i in range(n)]


class Round:
    """One fold round: degree bound d, weights on coefficients below `low`, points (theta', zeta)."""

    def __init__(self, fld, d, low, rng):
        self.f, self.d, self.low, self.rng = fld, d, low, rng
        self.w = [[rng.randrange(fld.q) for _ in range(low)] for _ in range(2)]

    def inner(self, iota, poly):
        f = self.f
        r = 0
        for c in range(min(self.low, len(poly))):
            r ^= f.mul(self.w[iota][c], poly[c])
        return r

    def fold(self, F, G, al, be):
        f = self.f
        out = list(G) + [0] * (self.d + 1 - len(G))
        for i, c in enumerate(F):
            out[i] ^= f.mul(al, c)
            out[i + 1] ^= f.mul(be, c)
        return out

    def wins(self, cands, points, v, phi, msg, sigma, zero_weight=False):
        """Brute force over all challenges. cands: list of functions (alpha, beta) -> polynomial or None."""
        f = self.f
        vG, vF, s0, s1 = msg
        count = 0
        for al in range(f.q):
            for be in range(f.q):
                rhs_w = vG ^ f.mul(al, vG ^ sigma) ^ f.mul(f.mul(al, al), vF) ^ f.mul(be, s0) ^ f.mul(f.mul(al, be), s0 ^ s1)
                for cand in cands:
                    P = cand(al, be)
                    if P is None:
                        continue
                    ok = True
                    for (th, ze), vm, ph in zip(points, v, phi):
                        if f.ev(P, ze) != vm ^ f.mul(th ^ al ^ f.mul(be, ze), ph):
                            ok = False
                            break
                    if not ok:
                        continue
                    if not zero_weight:
                        lhs = f.mul(1 ^ al, self.inner(0, P)) ^ f.mul(al, self.inner(1, P))
                        if lhs != rhs_w:
                            continue
                    count += 1
                    break
        return count


def member_cand(rnd, F, G):
    return lambda al, be: rnd.fold(F, G, al, be)


def make_family(fld, rng, d, k, r, low, share_low=False, affine_line=False):
    """F, G, R with r distinct roots, and k members (F, G + R H_a); with share_low, G_a = G + X^low H_a instead; with
    affine_line the H_a are constants times one polynomial, so the members lie on one affine line G + h Delta."""
    q = fld.q
    F = [rng.randrange(q) for _ in range(d)]
    G = [rng.randrange(q) for _ in range(d + 1)]
    roots = rng.sample(range(1, q), r)
    R = [1]
    for rho in roots:
        R = fld.pmul(R, [rho, 1])
    members = []
    seen = set()
    while len(members) < k:
        if share_low:
            H = [rng.randrange(q) for _ in range(d + 1 - low)]
            D = [0] * low + H
        elif affine_line:
            if not seen:
                base = [rng.randrange(1, q) for _ in range(d - r + 1)]
            h = rng.randrange(1, q)
            D = fld.pmul(R, [fld.mul(h, c) for c in base])
        else:
            H = [rng.randrange(q) for _ in range(d - r + 1)]
            D = fld.pmul(R, H)
        if tuple(D) in seen or not any(D):
            continue
        seen.add(tuple(D))
        members.append(padd(G, D))
    return F, G, roots, members


def honest_msg(rnd, F, G):
    XF = [0] + list(F)
    return (rnd.inner(0, G), rnd.inner(0, F) ^ rnd.inner(1, F), rnd.inner(0, XF), rnd.inner(1, XF))


def true_sigma(rnd, F, G):
    return rnd.inner(0, F) ^ rnd.inner(1, G)


def false_sigma(rnd, F, members, rng):
    vals = {true_sigma(rnd, F, G) for G in members}
    while True:
        s = rng.randrange(rnd.f.q)
        if s not in vals:
            return s


def line_setup(rnd, F, members, points, i, rng):
    """Note 16's answers: honest and common at the points m != i, off for every member at point i."""
    f = rnd.f
    v, phi = [], []
    for m, (th, ze) in enumerate(points):
        if m != i:
            vals = {f.mul(th, f.ev(F, ze)) ^ f.ev(G, ze) for G in members}
            assert len(vals) == 1, "members must share the answers at the special points"
            v.append(vals.pop())
        else:
            taken = {f.mul(th, f.ev(F, ze)) ^ f.ev(G, ze) for G in members}
            v.append(next(x for x in range(f.q) if x not in taken))
        phi.append(f.ev(F, ze))
    return v, phi


_ROOTMASK = {}


def exact_max_lines(rnd, lines, sigma, x_slope, phi_dependent):
    """Exact maximum over (v_G, v_F, sigma_0, sigma_1) (and over phi_i when `phi_dependent` gives the lines as a
    function of it) of the number of challenges on the given lines that satisfy (w).

    A line is (gamma, lhs) with alpha = gamma + beta * x_slope on it and lhs = (l0, l1, l2), the coefficients in beta
    of the left side of (w) for the line's candidate. The right side restricted to the line is
      [vG (1 + gamma) + gamma sigma + gamma^2 vF] + beta [x (vG + sigma) + s0 + gamma s01] + beta^2 [x^2 vF + x s01],
    s01 = sigma_0 + sigma_1."""
    f = rnd.f
    q = f.q
    mul = f.mul
    # root sets of c0 + c1 b + c2 b^2 as bit masks over beta
    rootmask = _ROOTMASK.setdefault(q, {})
    for c0 in range(q) if not rootmask else ():
        for c1 in range(q):
            for c2 in range(q):
                mk = 0
                for b in range(q):
                    if c0 ^ mul(c1, b) ^ mul(c2, mul(b, b)) == 0:
                        mk |= 1 << b
                rootmask[(c0, c1, c2)] = mk
    x = x_slope
    x2 = mul(x, x)
    best, arg = -1, None
    for phi_i, lines_phi in phi_dependent(lines):
        if not lines_phi:
            continue
        for vF in range(q):
            for s01 in range(q):
                r2 = mul(x2, vF) ^ mul(x, s01)
                for vG in range(q):
                    part0 = [(g, mul(vG, 1 ^ g) ^ mul(g, sigma) ^ mul(mul(g, g), vF) ^ l0, mul(x, vG ^ sigma) ^ mul(g, s01) ^ l1, r2 ^ l2)
                             for g, (l0, l1, l2) in lines_phi]
                    for s0 in range(q):
                        by_gamma = {}
                        for g, c0, c1p, c2 in part0:
                            by_gamma[g] = by_gamma.get(g, 0) | rootmask[(c0, c1p ^ s0, c2)]
                        tot = sum(bin(mk).count("1") for mk in by_gamma.values())
                        if tot > best:
                            best, arg = tot, (phi_i, vG, vF, s0, s0 ^ s01)
    return best, arg


def member_lhs_on_line(rnd, F, G, gamma, zeta):
    """Coefficients in beta of <(1+alpha) W_0 + alpha W_1, G + alpha F + beta X F> on alpha = gamma + beta zeta."""
    f = rnd.f
    mul = f.mul
    XF = [0] + list(F)
    A, B = rnd.inner(0, G), rnd.inner(1, G)
    C0, C1, D0, D1 = rnd.inner(0, F), rnd.inner(1, F), rnd.inner(0, XF), rnd.inner(1, XF)
    k1, k2, k11 = A ^ B ^ C0, C0 ^ C1, D0 ^ D1
    return (A ^ mul(gamma, k1) ^ mul(mul(gamma, gamma), k2), mul(zeta, k1) ^ D0 ^ mul(gamma, k11), mul(mul(zeta, zeta), k2) ^ mul(zeta, k11))


def lines_experiment(fld, rng, d, low, k, r, s, share_low, claim_true, label, zeta_zero=False, affine_line=False):
    """X4b, X4c, X4d at a small field, exact maximum; returns (best, k q, 2 q)."""
    rnd = Round(fld, d, low, rng)
    F, G, roots, members = make_family(fld, rng, d, k, r, low, share_low, affine_line)
    q = fld.q
    if share_low:
        special = [(rng.randrange(1, q), rng.randrange(q)) for _ in range(s - 1)]
        # the members differ by X^low H_a: make them share the answers at the special points by taking H_a with
        # roots there (H_a = Z * h_a, Z vanishing at the special zetas)
        Z = [1]
        for _th, ze in special:
            Z = fld.pmul(Z, [ze, 1])
        members = []
        seen = set()
        while len(members) < k:
            h = [rng.randrange(q) for _ in range(d + 1 - low - (s - 1))]
            D = [0] * low + fld.pmul(Z, h)
            if tuple(D) in seen or not any(D):
                continue
            seen.add(tuple(D))
            members.append(padd(G, D))
    else:
        special = [(rng.randrange(1, q), roots[m]) for m in range(s - 1)]
    while True:
        # zeta = 0 is a degenerate point (a_c(0) = alpha does not involve beta); it gets an experiment of its own
        free = (rng.randrange(1, q), 0 if zeta_zero else rng.randrange(1, q))
        if len({fld.ev(Gm, free[1]) for Gm in members}) == k and free[1] not in [z for _t, z in special]:
            break
        if zeta_zero:
            F, G, roots, members = make_family(fld, rng, d, k, r, low, share_low)
            special = [(rng.randrange(1, q), roots[m]) for m in range(s - 1)]
    points = special + [free]
    i = s - 1
    v, phi = line_setup(rnd, F, members, points, i, rng)
    sigma = true_sigma(rnd, F, members[0]) if claim_true else false_sigma(rnd, F, members, rng)
    if claim_true:
        assert len({true_sigma(rnd, F, Gm) for Gm in members}) == 1
    th, ze = points[i]
    Fz = fld.ev(F, ze)

    def per_phi(_):
        for ph in range(q):
            if ph == Fz:
                continue
            den = fld.inv(Fz ^ ph)
            out = []
            for Gm in members:
                gamma = fld.mul(v[i] ^ fld.mul(th, ph) ^ fld.ev(Gm, ze), den)
                out.append((gamma, member_lhs_on_line(rnd, F, Gm, gamma, ze)))
            yield ph, out

    best, arg = exact_max_lines(rnd, None, sigma, ze, per_phi)
    # cross-check the restriction against the brute-force definition at the optimum and at random messages
    cands = [member_cand(rnd, F, Gm) for Gm in members]
    tests = [arg] + [tuple(rng.randrange(q) for _ in range(5)) for _ in range(6)]
    for ph, vG, vF, s0, s1 in tests:
        if ph == Fz:
            continue
        phis = list(phi)
        phis[i] = ph
        brute = rnd.wins(cands, points, v, phis, (vG, vF, s0, s1), sigma)
        den = fld.inv(Fz ^ ph)
        pred = {}
        for Gm in members:
            gamma = fld.mul(v[i] ^ fld.mul(th, ph) ^ fld.ev(Gm, ze), den)
            l0, l1, l2 = member_lhs_on_line(rnd, F, Gm, gamma, ze)
            c0 = fld.mul(vG, 1 ^ gamma) ^ fld.mul(gamma, sigma) ^ fld.mul(fld.mul(gamma, gamma), vF) ^ l0
            c1 = fld.mul(ze, vG ^ sigma) ^ s0 ^ fld.mul(gamma, s0 ^ s1) ^ l1
            c2 = fld.mul(fld.mul(ze, ze), vF) ^ fld.mul(ze, s0 ^ s1) ^ l2
            mk = pred.get(gamma, set())
            mk |= {b for b in range(q) if c0 ^ fld.mul(c1, b) ^ fld.mul(c2, fld.mul(b, b)) == 0}
            pred[gamma] = mk
        assert brute == sum(len(mk) for mk in pred.values()), "restriction to lines disagrees with the brute force"
    zero = rnd.wins(cands, points, v, [phi[m] if m != i else (Fz ^ 1) for m in range(s)], (0, 0, 0, 0), 0, zero_weight=True)
    print(f"  {label}: q = {q}, k = {k}, s = {s}: zero weight {zero} (k q = {k * q}); with the weight, exact maximum over all q^5 messages = {best}"
          f"  (2q = {2 * q}, k q = {k * q})")
    return best, zero

def pole_experiment(fld, rng, dd=7, lo=4, nl=4):
    """nl pole lines alpha + beta x0 = gamma_a with close codewords G_a + beta Phi, G_a = (R_a + gamma_a Phi)/(X + x0),
    R_a = C0 + R H_a of degree <= d + 1, both points at roots of R so that every line shares both answers."""
    qq = fld.q
    rnd5 = Round(fld, dd, lo, rng)
    x0 = rng.randrange(1, qq)
    while True:
        Phi = [rng.randrange(qq) for _ in range(dd + 1)]
        if fld.ev(Phi, x0):
            break
    Phi = [fld.mul(c, fld.inv(fld.ev(Phi, x0))) for c in Phi]  # Phi(x0) = 1
    C0 = [rng.randrange(qq) for _ in range(dd + 2)]
    rts = rng.sample([x for x in range(1, qq) if x != x0], 2)
    R = fld.pmul([rts[0], 1], [rts[1], 1])
    lines, cands5, gammas = [], [], set()
    while len(lines) < nl:
        H = [rng.randrange(qq) for _ in range(dd)]  # deg R_a <= d + 1
        Ra = padd(C0, fld.pmul(R, H))
        gamma = fld.ev(Ra, x0)
        if gamma in gammas:
            continue
        gammas.add(gamma)
        num = padd(Ra, [fld.mul(gamma, c) for c in Phi])  # divisible by X + x0
        Ga, rem = [0] * (len(num) - 1), 0
        for idx in range(len(num) - 1, 0, -1):
            rem = num[idx] ^ fld.mul(rem, x0)
            Ga[idx - 1] = rem
        assert num[0] ^ fld.mul(rem, x0) == 0
        A, B, E0, E1 = rnd5.inner(0, Ga), rnd5.inner(1, Ga), rnd5.inner(0, Phi), rnd5.inner(1, Phi)
        lhs = (A ^ fld.mul(gamma, A ^ B), fld.mul(x0, A ^ B) ^ E0 ^ fld.mul(gamma, E0 ^ E1), fld.mul(x0, E0 ^ E1))
        lines.append((gamma, lhs))

        def cand(al, be, gamma=gamma, Ga=Ga):
            if al ^ fld.mul(be, x0) != gamma:
                return None
            return padd(Ga, [fld.mul(be, c) for c in Phi])

        cands5.append(cand)
    sig5 = rng.randrange(qq)
    best5, arg5 = exact_max_lines(rnd5, lines, sig5, x0, lambda ls: [(0, ls)])
    # the points: both at roots of R; answers consistent with every line: y^F = Phi(z)/(x0+z), y^G = C0(z)/(x0+z)
    pts5 = [(rng.randrange(1, qq), z) for z in rts]
    v5, phi5 = [], []
    for th, ze in pts5:
        den = fld.inv(x0 ^ ze)
        yF, yG = fld.mul(fld.ev(Phi, ze), den), fld.mul(fld.ev(C0, ze), den)
        phi5.append(yF)
        v5.append(yG ^ fld.mul(th, yF))
    _ph, vG, vF, s0, s1 = arg5
    brute5 = rnd5.wins(cands5, pts5, v5, phi5, (vG, vF, s0, s1), sig5)
    allp = rnd5.wins(cands5, pts5, v5, phi5, (0, 0, 0, 0), 0, zero_weight=True)
    assert brute5 == best5, (brute5, best5)
    return best5, allp, nl, qq


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    rng = random.Random(seed)
    f8 = Field(8, 0b100011101)  # x^8 + x^4 + x^3 + x^2 + 1, primitive
    f4 = Field(4, 0b10011)
    q = f8.q
    d, low, k, r = 9, 6, 5, 3
    print(f"GF(2^8), q = {q}, d = {d}, weights on the {low} low coefficients, k = {k} members, R of degree {r}; q^2 = {q * q} challenges")

    # X1: no points
    rnd = Round(f8, d, low, rng)
    F, G, roots, members = make_family(f8, rng, d, k, r, low)
    cands = [member_cand(rnd, F, Gm) for Gm in members]
    sigma = false_sigma(rnd, F, members, rng)
    msg = honest_msg(rnd, F, members[0])
    w1 = rnd.wins(cands, [], [], [], msg, sigma)
    print(f"  X1  no point claims, message honest for F, false claim: {w1} wins (k q = {k * q}): the list attack")

    # X2: generic points answered for member 1
    for s in (1, 2, 3):
        pts = [(rng.randrange(1, q), rng.choice([x for x in range(q) if x not in roots])) for _ in range(s)]
        v = [f8.mul(th, f8.ev(F, ze)) ^ f8.ev(members[0], ze) for th, ze in pts]
        phi = [f8.ev(F, ze) for _th, ze in pts]
        w2 = rnd.wins(cands, pts, v, phi, msg, sigma)
        print(f"  X2  s = {s} generic points answered for member 1, same message: {w2} wins (q = {q}, 2q = {2 * q})")

    # X3: clique, all points at roots of R
    for s in (1, 2, 3):
        pts = [(rng.randrange(1, q), roots[m]) for m in range(s)]
        v = [f8.mul(th, f8.ev(F, ze)) ^ f8.ev(members[0], ze) for th, ze in pts]
        phi = [f8.ev(F, ze) for _th, ze in pts]
        w3 = rnd.wins(cands, pts, v, phi, msg, sigma)
        print(f"  X3  s = {s} points at roots of R (probability (r/q)^s), same message: {w3} wins (k q = {k * q})")

    # X4a at q = 256: zero weight, s - 1 roots
    for s in (2, 3):
        pts = [(rng.randrange(1, q), roots[m]) for m in range(s - 1)]
        while True:
            free = (rng.randrange(1, q), rng.randrange(q))
            if free[1] not in roots and len({f8.ev(Gm, free[1]) for Gm in members}) == k:
                break
        pts.append(free)
        v, phi = line_setup(rnd, F, members, pts, s - 1, rng)
        phi[s - 1] ^= 1
        w4 = rnd.wins(cands, pts, v, phi, (0, 0, 0, 0), 0, zero_weight=True)
        print(f"  X4a s = {s}, s-1 points at roots (probability s (r/q)^(s-1)), one answer off, zero weight: {w4} wins (k q = {k * q})")

    print(f"GF(2^4), q = 16, exact maxima over all q^5 = {16**5} prover messages")
    for kk in (3, 4):
        lines_experiment(f4, rng, 7, 4, kk, 2, 2, False, False, f"X4b members U_1 + R H_a, false claim, k = {kk}")
    lines_experiment(f4, rng, 7, 4, 5, 2, 2, False, False, "X4b members U_1 + R H_a, false claim, k = 5")
    lines_experiment(f4, rng, 7, 4, 3, 2, 3, False, False, "X4b the same with three points, k = 3")
    lines_experiment(f4, rng, 7, 4, 4, 2, 2, False, False, "X4b' the free point has zeta = 0 (probability 1/q), k = 4", zeta_zero=True)
    lines_experiment(f4, rng, 7, 4, 4, 2, 2, False, False, "X4e members on one affine line G + h R H, false claim, k = 4", affine_line=True)
    lines_experiment(f4, rng, 7, 4, 6, 2, 3, False, False, "X4e the same with three points, k = 6", affine_line=True)
    lines_experiment(f4, rng, 7, 4, 4, 2, 2, True, True, "X4c members sharing the low part, TRUE claim")
    lines_experiment(f4, rng, 7, 4, 4, 2, 2, True, False, "X4d members sharing the low part, FALSE claim")

    # X5: pole lines sharing all answers, random weight, exact maximum over (vG, vF, s0, s1), twelve instances
    hist = {}
    for _ in range(12):
        best5, zero5, nl, qq = pole_experiment(f4, rng)
        assert zero5 == nl * qq
        hist[best5] = hist.get(best5, 0) + 1
    print(f"  X5  4 pole lines sharing both answers (points at roots of R), q = 16: zero weight {4 * 16} wins (N q); random weight, exact maximum over all "
          f"q^4 messages, 12 instances: " + ", ".join(f"{v} wins in {c}" for v, c in sorted(hist.items()))
          + "  (q + 3 = 19: one line; 2q + 2 = 34: two lines, which needs one coincidence of probability about 1/q per pair of lines)")


if __name__ == "__main__":
    main()
