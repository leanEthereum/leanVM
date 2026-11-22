"""Note 38, section 4 (attack W2): with two points per level and a weighted claim chosen by the adversary,
every list member through one domain column wins its own line of fold challenges.
Toy: E = GF(2^8), D = span(1..x^4) (n = 32), rate 1/4 (degree bound 8), one fold round with one lane per half.
Word O = (F, w): O_0 = F exactly (degree <= 7), O_1 = w = X^16 on D. Members U_a = (F, C_a), C_a = X^16 + L_H
for the 62 affine hyperplanes H (degree <= 8, agreement 16 = n/2). Point 1 has zeta_1 in D, point 2 is generic
and its answer is matched by no member. The weight is evaluation at zeta_2 on both halves (scalars m, m'),
the claim sigma is false for every member. Winning challenges are counted by brute force over all q^2
challenges from the definitions (p) and (w) of Lemma 4.10 of the paper."""
import random, sys, importlib
sys.path.insert(0, sys.path[0])
gfm = importlib.import_module("38_gf")
F = gfm.GF(8)
q, N, n, d = 256, 5, 32, 8
mul, inv, ev = F.mul, F.inv, F.ev
par = lambda v: bin(v).count("1") & 1


def run(seed, zeta1_in_D=True, weight="point"):
    rnd = random.Random(seed)
    F0 = [rnd.randrange(q) for _ in range(d)]                        # degree <= 7
    members = []
    for a in range(1, n):
        for c in (0, 1):
            H = [x for x in range(n) if par(a & x) == c]
            C = gfm.padd([0] * 16 + [1], F.locator(H))
            assert gfm.deg(C) <= d
            members.append((H, C[: d + 1]))
    w = lambda x: F.exp[(16 * F.log[x]) % 255] if x else 0
    z1 = rnd.randrange(1, n) if zeta1_in_D else rnd.randrange(n, q)
    z2 = rnd.randrange(n, q)
    th1, th2 = rnd.randrange(1, q), rnd.randrange(1, q)
    F1, F2 = ev(F0, z1), ev(F0, z2)
    g = [ev(C, z2) for _, C in members]
    thru = [i for i, (H, _) in enumerate(members) if z1 in H]
    # answers: honest and common at point 1 (the column of the word), unmatched at point 2
    v1, phi1 = mul(th1, F1) ^ w(z1), F1
    taken = {mul(th2, F2) ^ gi for gi in g}
    v2 = next(v for v in range(1, q) if v not in taken)
    u = v2 ^ mul(th2, F2)
    m, mp = rnd.randrange(1, q), rnd.randrange(1, q)
    if weight == "point":                                            # W_0 = m ev_{zeta_2}, W_1 = m' ev_{zeta_2}
        W0 = lambda P: mul(m, ev(P, z2))
        W1 = lambda P: mul(mp, ev(P, z2))
    else:                                                            # weights independent of the members
        r0 = [rnd.randrange(q) for _ in range(d + 2)]
        r1 = [rnd.randrange(q) for _ in range(d + 2)]
        dot = lambda r, P: __import__("functools").reduce(lambda x, y: x ^ y, (mul(a, b) for a, b in zip(r, P)), 0)
        W0, W1 = (lambda P: dot(r0, P)), (lambda P: dot(r1, P))
    XF = [0] + F0
    w0F, w1F, w0X, w1X = W0(F0), W1(F0), W0(XF), W1(XF)
    while True:
        sigma = rnd.randrange(q)
        false_all = all(w0F ^ W1(C) ^ sigma for _, C in members)
        if false_all and (mul(mp, th2) ^ m) and (w0F ^ sigma ^ mul(mp, u)):
            break
    # the message of Proposition R3(b) of note 20 (c = c' = 0)
    t = mul(mul(mp, th2) ^ m, inv(w0F ^ sigma ^ mul(mp, u)))
    s = mul(m, inv(t))
    p = mul(mp, inv(t)) ^ s
    vG = mul(s, th2) ^ mul(m, u)
    vF = w0F ^ w1F ^ p
    sig0 = w0X ^ mul(z2, s)
    sig1 = w1X ^ mul(z2, p) ^ mul(z2, s)
    phi2 = F2 ^ inv(t)
    pre = [(ev(C, z1), g[i], W0(C), W1(C)) for i, (_, C) in enumerate(members)]
    wins, per = 0, [0] * len(members)
    for al in range(q):
        al2 = mul(al, al)
        for be in range(q):
            a1, a2 = al ^ mul(be, z1), al ^ mul(be, z2)
            r1 = v1 ^ mul(th1 ^ a1, phi1)
            r2 = v2 ^ mul(th2 ^ a2, phi2)
            rhs = vG ^ mul(al, vG ^ sigma) ^ mul(al2, vF) ^ mul(be, sig0) ^ mul(mul(al, be), sig0 ^ sig1)
            won = False
            for i, (c1, c2, x0, x1) in enumerate(pre):
                if c1 ^ mul(a1, F1) != r1 or c2 ^ mul(a2, F2) != r2:
                    continue
                # <(1+al) W_0 + al W_1, C + (al + be X) F>
                lhs = mul(1 ^ al, x0 ^ mul(al, w0F) ^ mul(be, w0X)) ^ mul(al, x1 ^ mul(al, w1F) ^ mul(be, w1X))
                if lhs == rhs:
                    won = True
                    per[i] += 1
            wins += won
    full = sum(1 for x in per if x >= q)
    return wins, len(thru), full, sorted(set(per))


if __name__ == "__main__":
    for seed in (1, 2, 3):
        wins, k, full, hist = run(seed)
        print(f"seed {seed}: zeta_1 in D, weight = evaluation at zeta_2, claim false for all 62 members: "
              f"{wins} winning challenges of {q*q}; members through the column k = {k}, k*q = {k*q}; "
              f"members with a whole line: {full}; per-member counts {hist}")
    for seed in (1, 2):
        wins, k, full, hist = run(seed, weight="generic")
        print(f"seed {seed}: same with a weight independent of the members (same message recipe, not optimal): {wins} winning challenges; whole lines: {full}")
    wins, k, full, hist = run(1, zeta1_in_D=False)
    print(f"control, zeta_1 outside D (v_1 then matches no member): {wins} winning challenges; whole lines: {full}")
