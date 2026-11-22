#!/usr/bin/env python3
"""Referee check 3 (note 20): Protocol D_S (the ladder of note 15) run end to end on the toy of note 11.

This is `11_protocol_toy.py` (note 11's toy of Protocol D: two levels, level boundary, conversion of the point claims,
queries, tail sumcheck, terminal weight unrolled) with one change: a level has a schedule of batches. Batch 1 is
sampled after the commitment, batch b >= 2 is sampled with the fold challenge of round b - 1 and answered on the
tuple after b - 1 rounds (ev^(b-1), lane variables b..ell), and every round carries one phi for every point held so
far. Note 15 checked the algebra of one level (`15_batch_toy.py`); this run adds the level boundary (all
sigma_ell claims converted and batched with the queries), the last level's point checks on the polynomial sent, and
the terminal weight.

  level 0: nu = 7, ell = 3, kappa = 4, rate 1/2 (n = 32), batches 2 + 1 + 2, t = 4 queries
  level 1: ell = 2, kappa = 2, rate 1/8 (n = 32), batches 1 + 2, t = 3 queries; then a sumcheck on 2 variables

Checked on every honest run: C1 to C5 of note 11's toy, with C2 and C3 for every point of every batch. Tampered runs
(one answer of a late batch, one phi of a late point, an answer of batch 1, a round value, a high coefficient) must be
rejected by a verifier check.

Usage: python3 20_ladder_toy.py [seed]
"""
import random
import sys

M, MOD = 16, (1 << 16) | 0b101101
EXP, LOG = [0] * (2 << M), [0] * (1 << M)
_v = 1
for _i in range((1 << M) - 1):
    EXP[_i], LOG[_v] = _v, _i
    _v <<= 1
    if _v >> M:
        _v ^= MOD
for _i in range((1 << M) - 1, 2 << M):
    EXP[_i] = EXP[_i - ((1 << M) - 1)]


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[(1 << M) - 1 - LOG[a]]


def fsum(xs):
    r = 0
    for x in xs:
        r ^= x
    return r


# Annex D: W_i(e_i) for i <= 16 (e_i = x^i = 1 << i), by W_(i+1) = W_i^2 + W_i(e_i) W_i.
ROOTS = [1]
_layer = [1 << i for i in range(1, M)]
for _ in range(M - 1):
    _root = ROOTS[-1]
    _layer = [mul(v, v) ^ mul(_root, v) for v in _layer]
    ROOTS.append(_layer.pop(0))


def what(x, count):
    """What_0(x), ..., What_(count-1)(x), for any x in the field."""
    out, basis = [], x
    for i in range(count):
        out.append(mul(basis, inv(ROOTS[i])))
        basis = mul(basis, basis) ^ mul(ROOTS[i], basis)
    return out


def novel_eval(coeffs, x):
    """P(x) for P = sum_c coeffs[c] X_c."""
    w = what(x, max(len(coeffs) - 1, 1).bit_length())
    total = 0
    for c, p in enumerate(coeffs):
        term = p
        for i, wi in enumerate(w):
            if (c >> i) & 1:
                term = mul(term, wi)
        total ^= term
    return total


def times_x(h):
    """Novel-basis coefficients of X H (Annex D, Lemma lem:mulx)."""
    get = lambda c: h[c] if 0 <= c < len(h) else 0
    out = [0] * (len(h) + 1)
    for c in range(1, len(h) + 1):
        s = (c & -c).bit_length() - 1
        coef = 1
        for d in range(s):
            coef = mul(coef, mul(ROOTS[d + 1], inv(mul(ROOTS[d], ROOTS[d]))))
        out[c] = mul(coef, get(c - 1) ^ get(c + (1 << s) - 1))
    return out


def mle(table, point):
    """Multilinear extension of a table, variable k = bit k of the index."""
    for p in point:
        table = [mul(1 ^ p, table[2 * r]) ^ mul(p, table[2 * r + 1]) for r in range(len(table) // 2)]
    assert len(table) == 1
    return table[0]


def col_weight(x, kappa):
    """W_x on kappa variables as a table: W_x[c] = prod_k What_k(x)^(c_k) (Lemma lem:colweight, any x in E)."""
    w, table = what(x, kappa), [1]
    for wi in w:
        table = table + [mul(t, wi) for t in table]
    return table


def col_weight_at(x, point):
    """The extension of W_x at `point` in O(kappa): prod_k ((1 + p_k) + p_k What_k(x))."""
    out = 1
    for p, wi in zip(point, what(x, len(point))):
        out = mul(out, 1 ^ p ^ mul(p, wi))
    return out


def inner(weight, lanes, kappa):
    """<W, P> on the low parts: W indexed by lane bits low, then the coefficient index."""
    m = len(lanes)
    return fsum(mul(weight[u + m * c], lanes[u][c]) for u in range(m) for c in range(1 << kappa))


def ev(theta, zeta, lanes, first):
    """ev_z of a tuple whose lane variables are numbered first, first + 1, ...: sum_u theta^e(u) P_u(zeta),
    e(u) = sum_k (1 - u_k) 2^(k-1)."""
    total, nvars = 0, (len(lanes) - 1).bit_length()
    for u, lane in enumerate(lanes):
        e = sum((1 - ((u >> b) & 1)) << (first - 1 + b) for b in range(nvars))
        total ^= mul(EXP[(LOG[theta] * e) % ((1 << M) - 1)] if theta else (1 if e == 0 else 0), novel_eval(lane, zeta))
    return total


class Reject(Exception):
    pass


def require(cond, what_failed):
    if not cond:
        raise Reject(what_failed)


LEVELS = [dict(ell=3, kappa=4, rate=1, batches=[2, 1, 2], t=4), dict(ell=2, kappa=2, rate=3, batches=[1, 2], t=3)]
NU = 7
J0 = 3


def run(seed, tamper=None):
    """One interactive run. Returns the number of completeness assertions checked. `tamper` names one prover value to
    alter; the run must then end in Reject."""
    rng = random.Random(seed)
    rnd = lambda: rng.randrange(1, 1 << M)
    checks = 0
    f = [rnd() for _ in range(1 << NU)]
    in_weights = [[rnd() for _ in range(1 << NU)] for _ in range(J0)]
    in_values = [fsum(mul(w, x) for w, x in zip(wt, f)) for wt in in_weights]

    # ---- commitment of level 0, its points and answers ----
    message = f
    lam0 = None
    alphas = []
    glued = []  # verifier: (scalar, fold_start, kind, x) with kind 'col'
    v_claim = None  # verifier's running claim
    p_weight = None  # prover's running weight table
    for i, lv in enumerate(LEVELS):
        ell, kappa, rate, batches, t = lv["ell"], lv["kappa"], lv["rate"], lv["batches"], lv["t"]
        s = batches[0]
        final = i == len(LEVELS) - 1
        n = 1 << (kappa + rate)
        lanes = [[message[u + (1 << ell) * c] for c in range(1 << kappa)] for u in range(1 << ell)]
        oracle = [[novel_eval(lane, x) for x in range(n)] for lane in lanes]  # rows = lanes, columns = D
        points = [(rnd(), rnd()) for _ in range(s)]
        answers = [ev(th, ze, lanes, 1) for th, ze in points]
        if tamper == ("answer", i):
            answers[0] ^= 1
        carried = list(answers)  # verifier's v_m
        if i == 0:
            lam0 = rnd()
            p_weight = [fsum(mul(EXP[(LOG[lam0] * k) % ((1 << M) - 1)], in_weights[k][r]) for k in range(J0)) for r in range(1 << NU)]
            v_claim = fsum(mul(EXP[(LOG[lam0] * k) % ((1 << M) - 1)], in_values[k]) for k in range(J0))
        rounds = []
        for j in range(1, ell + 1):
            half = len(lanes) // 2
            big_f, big_g = [lanes[2 * u] for u in range(half)], [lanes[2 * u + 1] for u in range(half)]
            xf = [times_x(p) for p in big_f]
            w0, w1 = p_weight[0::2], p_weight[1::2]
            v_g = inner(w0, big_g, kappa)
            v_f = inner([a ^ b for a, b in zip(w0, w1)], big_f, kappa)
            sig0, sig1 = inner(w0, xf, kappa), inner(w1, xf, kappa)
            if j >= 2 and batches[j - 1]:
                # batch j: sampled with the fold challenge of round j - 1, answered on the tuple after j - 1 rounds
                fresh = [(rnd(), rnd()) for _ in range(batches[j - 1])]
                fresh_answers = [ev(th, ze, lanes, j) for th, ze in fresh]
                if tamper == ("late_answer", i, j):
                    fresh_answers[0] ^= 1
                points = points + fresh
                carried = carried + fresh_answers
            phis = [ev(th, ze, big_f, j + 1) for th, ze in points]
            if tamper == ("phi", i, j):
                phis[-1] ^= 1
            if tamper == ("round", i, j):
                v_f ^= 1
            alpha, beta = rnd(), rnd()
            # verifier
            v_claim = v_g ^ mul(alpha, v_g ^ v_claim) ^ mul(mul(alpha, alpha), v_f) ^ mul(beta, sig0) ^ mul(mul(alpha, beta), sig0 ^ sig1)
            for m_, (th, ze) in enumerate(points):
                th_j = EXP[(LOG[th] << (j - 1)) % ((1 << M) - 1)]
                carried[m_] ^= mul(th_j ^ alpha ^ mul(beta, ze), phis[m_])
            alphas.append(alpha)
            rounds.append((alpha, beta))
            # prover
            lanes = [[g ^ mul(alpha, a) ^ mul(beta, b) for g, a, b in zip(big_g[u] + [0], big_f[u] + [0], xf[u])] for u in range(half)]
            p_weight = [mul(1 ^ alpha, a) ^ mul(alpha, b) for a, b in zip(w0, w1)]
            if tamper is None:
                assert v_claim == inner(p_weight, lanes, kappa), "C1"
                assert all(carried[m_] == ev(th, ze, lanes, j + 1) for m_, (th, ze) in enumerate(points)), "C2"
                checks += 1 + len(points)
        folded = lanes[0]
        assert len(folded) == (1 << kappa) + ell

        def fold_column(x):
            col = [row[x] for row in oracle]
            for alpha, beta in rounds:
                a = alpha ^ mul(beta, x)
                col = [col[2 * u + 1] ^ mul(a, col[2 * u]) for u in range(len(col) // 2)]
            return col[0]

        if tamper is None:
            assert all(fold_column(x) == novel_eval(folded, x) for x in range(n)), "C4"
            assert all(novel_eval(folded, ze) == carried[m_] for m_, (_th, ze) in enumerate(points)), "C3"
            assert len(points) == sum(batches)
            checks += n + len(points)
        low, high = folded[: 1 << kappa], folded[1 << kappa :]
        if final:
            # the final polynomial in the clear: point checks, queries, tail sumcheck, terminal check
            for m_, (_th, ze) in enumerate(points):
                require(novel_eval(folded, ze) == carried[m_], "final point claim")
            for _ in range(t):
                x = rng.randrange(n)
                require(fold_column(x) == novel_eval(folded, x), "final query")
            table_w, table_f, tail = list(p_weight), list(low), []
            for _ in range(kappa):
                g0 = fsum(mul(a, b) for a, b in zip(table_w[0::2], table_f[0::2]))
                c2 = fsum(mul(a0 ^ a1, b0 ^ b1) for a0, a1, b0, b1 in zip(table_w[0::2], table_w[1::2], table_f[0::2], table_f[1::2]))
                r = rnd()
                g1 = v_claim ^ g0
                v_claim = g0 ^ mul(g1 ^ g0 ^ c2, r) ^ mul(c2, mul(r, r))
                table_w = [mul(1 ^ r, a) ^ mul(r, b) for a, b in zip(table_w[0::2], table_w[1::2])]
                table_f = [mul(1 ^ r, a) ^ mul(r, b) for a, b in zip(table_f[0::2], table_f[1::2])]
                tail.append(r)
            # the verifier's weight at the terminal point, unrolled
            point = alphas + tail
            weight = fsum(mul(EXP[(LOG[lam0] * k) % ((1 << M) - 1)], mle(in_weights[k], point)) for k in range(J0))
            for scalar, start, x in glued:
                weight ^= mul(scalar, col_weight_at(x, point[start:]))
            if tamper is None:
                assert weight == table_w[0], "C5"
                checks += 1
            require(mul(weight, mle(low, tail)) == v_claim, "terminal check")
            return checks
        if tamper == ("high", i):
            high = [high[0] ^ 1] + high[1:]
        # ---- next commitment is `low`; then this level's queries and lambda ----
        lam = rnd()
        hat_k = lambda x: what(x, kappa + 1)[kappa]
        claims = []  # (weight point x, value): column weights of this level's code, at zeta's and at the queries
        for m_, (_th, ze) in enumerate(points):
            value = carried[m_] ^ mul(hat_k(ze), novel_eval(high, ze))
            claims.append((ze, value))
            if tamper is None:
                assert fsum(mul(a, b) for a, b in zip(col_weight(ze, kappa), low)) == value, "C3 converted"
                checks += 1
        for _ in range(t):
            x = rng.randrange(n)
            value = fold_column(x) ^ mul(hat_k(x), novel_eval(high, x))
            claims.append((x, value))
            if tamper is None:
                assert fsum(mul(a, b) for a, b in zip(col_weight(x, kappa), low)) == value, "C4 query"
                checks += 1
        power = 1
        for x, value in claims:
            power = mul(power, lam)
            v_claim ^= mul(power, value)
            glued.append((power, len(alphas), x))
            p_weight = [a ^ mul(power, b) for a, b in zip(p_weight, col_weight(x, kappa))]
        message = low
    raise AssertionError("no final level")


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    total = 0
    for k in range(20):
        total += run(seed + k)
    print(f"ladder, honest runs: 20 accepted, {total} completeness identities checked (C1 to C5)")
    tampers = [("answer", 0), ("late_answer", 0, 2), ("late_answer", 0, 3), ("late_answer", 1, 2), ("phi", 0, 2), ("phi", 0, 3), ("phi", 1, 2),
               ("round", 0, 2), ("round", 1, 1), ("high", 0)]
    for tamper in tampers:
        reasons = set()
        for k in range(20):
            try:
                run(seed + k, tamper)
                raise AssertionError(f"tampered run accepted: {tamper}")
            except Reject as e:
                reasons.add(str(e))
        print(f"tamper {tamper}: 20 of 20 rejected ({', '.join(sorted(reasons))})")
    print("ladder toy passed")


if __name__ == "__main__":
    main()
