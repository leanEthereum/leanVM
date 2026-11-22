#!/usr/bin/python3
# Referee 87: brute-force Kraft sum of the prefix code of note 84, Lemma 4.1 (options of Corollary 3.3(5)),
# enumerating every prefix label on tiny trees; multipliers from the backward recursion of Section 4.
import math, itertools

def multipliers(lam, eta, nD, v, J):
    C = Cp = 0.0
    out = {}
    for i in range(v - 1, J - 1, -1):
        B = (C - Cp) / 2
        li, ei = lam + B, eta - B
        c = math.log2(1 + 2 * nD * 2 ** -li + nD * (nD - 1) * 2 ** (-2 * li))
        cp = math.log2(1 + 2 ** (1 - ei) * (1 + (nD - 1) * 2 ** -li))
        out[i] = (li, ei, c, cp)
        C += c
        Cp += cp
    return out, 2 * lam + C - Cp

def options(node_dir, nD):
    """Options of one node: list of (children directions (d0, d1) with None = absent, tight count, half flag)."""
    opts = []
    if node_dir is None:
        opts.append(((None, None), 0, 0))
        for d in range(nD):
            opts.append(((d, None), 1, 0))
            opts.append(((None, d), 1, 0))
        for d0 in range(nD):
            for d1 in range(nD):
                if d0 != d1:
                    opts.append(((d0, d1), 2, 0))
        return opts, False
    lam_p = node_dir
    res = [((("R", lam_p), ("R", lam_p)), 0, 0)]  # doubling
    for b in (0, 1):
        ch = [None, None]
        ch[b] = ("R", lam_p)
        res.append((tuple(ch), 0, 1))  # other child absent
        for mu in range(nD):
            if mu != lam_p:
                ch2 = list(ch)
                ch2[1 - b] = mu
                res.append((tuple(ch2), 1, 1))  # other child tight with mu != lambda_p
    return res, True

def kraft(nJ, levels, nD, lam, eta, J):
    v = J + levels
    mult, lamJ = multipliers(lam, eta, nD, v, J)
    count = 0
    def rec(i, Y):
        # Y: tuple of directions (None or index) of the nodes of Y_i; returns sum of 2^-w over the options of levels i..v-1
        nonlocal count
        if i == v:
            count += 1
            return 1.0
        li, ei, c, cp = mult[i]
        m = sum(1 for d in Y if d is None)
        base = 2.0 ** -(m * c + (len(Y) - m) * cp)
        total = 0.0
        per_node = [options(d, nD)[0] for d in Y]
        for combo in itertools.product(*per_node):
            d_i = sum(o[1] for o in combo)
            h_i = sum(o[2] for o in combo)
            # Y_{i+1} is the system that Y_i and the options determine: rounded children (with the parent's
            # direction) and children declared tight (with their own direction).
            nxt = []
            for ch, _, _ in combo:
                for cdir in ch:
                    if cdir is None:
                        nxt.append(None)
                    elif isinstance(cdir, tuple):
                        nxt.append(cdir[1])
                    else:
                        nxt.append(cdir)
            total += 2.0 ** -(li * d_i + ei * h_i) * rec(i + 1, tuple(nxt))
        return base * total
    total = 0.0
    if J == 0:
        total = rec(0, tuple([None] * nJ))
    else:
        for Y in itertools.product([None] + list(range(nD)), repeat=nJ):
            sz = sum(1 for d in Y if d is not None)
            total += 2.0 ** -(lamJ * sz + nJ * math.log2(1 + nD * 2 ** -lamJ)) * rec(J, Y)
    return total, count

if __name__ == "__main__":
    for (nJ, levels, nD, lam, eta, J) in [(2, 2, 1, 1.3, 2.1, 0), (2, 2, 2, 0.7, 1.9, 0), (1, 3, 2, 1.1, 0.4, 0), (2, 2, 3, 2.0, 3.0, 0), (2, 1, 3, 0.9, 1.7, 1), (2, 2, 2, 1.5, 2.5, 1)]:
        s, cnt = kraft(nJ, levels, nD, lam, eta, J)
        print("n_J=%d levels=%d |Delta|=%d lam=%.1f eta=%.1f J=%d: %d labels, Kraft sum = %.12f" % (nJ, levels, nD, lam, eta, J, cnt, s))
