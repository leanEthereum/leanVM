#!/usr/bin/env python3
"""Note 14, section 5: the agreement-set extractor of Protocol D on a toy level, with corrupted commitments.

Standard library only, a few seconds. Field GF(2^16); one level with ell = 3 fold rounds, kappa = 4, rate 1/4:
n = 64 columns, 8 lanes, analysis degree d = 2^4 - 1 + 3 = 18, thresholds thr_j = A0 + j with A0 = 28.

The prover commits a word O that is NOT a codeword and plays the level honestly for one tuple U of its list.
The extractor sees the committed word, the fold challenges and the final polynomial, and descends: at each round
going back it takes the agreement set S of the current tuple with the folded word and decodes the near tuple of
the unfolded word on S (degree <= d, at most one column of S in error), by one-error decoding on the known set.
It never list-decodes. Predictions of the proof that are checked:

  X1  errors on n - A0 columns, no repaired column: the descent returns U at every round;
  X2  one column repaired by a fold challenge (its folded error vanishes, the event the agreement loss of one
      per round pays for): the agreement set gains a column where U is wrong, and the descent still returns U;
  X3  a word with TWO list members U, U' (each agreeing on at least A0 columns): the descent returns the member
      the run was played for, whichever it is, and the point answers of the two members differ (pinning);
  X4  two columns repaired by one challenge (probability at most C(n,2)/q^2, inside the fold error K0/q^2):
      no near tuple exists on the agreement set and the extractor reports failure;
  X5  the near tuple is unique: every leave-one-out candidate that passes is the same tuple.

Usage: python3 14_extractor_toy.py [seed]
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


ELL, KAPPA, RATE = 3, 4, 2
N = 1 << (KAPPA + RATE)
D = (1 << KAPPA) - 1 + ELL
A0 = 28


def horner(coeffs, x):
    r = 0
    for c in reversed(coeffs):
        r = mul(r, x) ^ c
    return r


def fold_table(rows, alpha, beta):
    """Affine fold of a table of lanes (rows[u][x]), lane variable folded first = low bit of u."""
    return [[rows[2 * u + 1][x] ^ mul(alpha ^ mul(beta, x), rows[2 * u][x]) for x in range(N)] for u in range(len(rows) // 2)]


def agreement(tuple_rows, word_rows):
    return [x for x in range(N) if all(t[x] == w[x] for t, w in zip(tuple_rows, word_rows))]


def interpolate_rows(word_rows, nodes):
    """The tuple of degree <= len(nodes) - 1 through the word on `nodes`, as evaluation tables on the domain."""
    wts = []
    for s in nodes:
        den = 1
        for t in nodes:
            if t != s:
                den = mul(den, s ^ t)
        wts.append(inv(den))
    node_set = set(nodes)
    ell_y, inv_diff = [], []
    for y in range(N):
        if y in node_set:
            ell_y.append(0)
            inv_diff.append(None)
            continue
        prod = 1
        for s in nodes:
            prod = mul(prod, y ^ s)
        ell_y.append(prod)
        inv_diff.append([inv(y ^ s) for s in nodes])
    out = []
    for row in word_rows:
        scaled = [mul(w, row[s]) for w, s in zip(wts, nodes)]
        vals = []
        for y in range(N):
            if y in node_set:
                vals.append(row[y])
            else:
                acc = 0
                for sc, iv in zip(scaled, inv_diff[y]):
                    acc ^= mul(sc, iv)
                vals.append(mul(ell_y[y], acc))
        out.append(vals)
    return out


def near_decode(word_rows, S, d, all_candidates=False):
    """One-error decoding on the known set S: the tuples of degree <= d that agree with the word on all but at
    most one column of S. Leave-one-out over the first d + 2 columns of S: if a near tuple exists, the column it
    misses is one of them or none of them, and in both cases some leave-one-out node set is clean."""
    assert len(S) >= d + 3
    head = S[: d + 2]
    found = []
    for skip in range(d + 2):
        nodes = head[:skip] + head[skip + 1 :]
        cand = interpolate_rows(word_rows, nodes)
        bad = [x for x in S if any(c[x] != w[x] for c, w in zip(cand, word_rows))]
        if len(bad) <= 1:
            if not all_candidates:
                return cand
            found.append(cand)
    if all_candidates:
        return found
    return None


def make_tuple(rng):
    return [[rng.randrange(1 << M) for _ in range(1 << KAPPA)] for _ in range(1 << ELL)]


def table_of(lanes):
    return [[horner(lane, x) for x in range(N)] for lane in lanes]


def ev_point(theta, zeta, lanes):
    """ev^(0)_z(U) = sum_u theta^e(u) U_u(zeta), e(u) = sum_k (1 - u_k) 2^(k-1), u_k = bit k-1 of the lane index."""
    total = 0
    for u, lane in enumerate(lanes):
        e = sum((1 - ((u >> b) & 1)) << b for b in range(ELL))
        total ^= mul(EXP[(LOG[theta] * e) % ((1 << M) - 1)], horner(lane, zeta))
    return total


def descend(word, challenges, final_rows):
    """The extractor for one level: returns the list of tuples reached going back (round ell - 1 down to 0), or
    None with the round at which it failed."""
    folded_words = [word]
    for alpha, beta in challenges:
        folded_words.append(fold_table(folded_words[-1], alpha, beta))
    cur, out = final_rows, []
    for j in range(len(challenges), 0, -1):
        S = agreement(cur, folded_words[j])
        if len(S) < A0 + j:
            return None, j, out
        cur = near_decode(folded_words[j - 1], S, D)
        if cur is None:
            return None, j, out
        out.append(cur)
    return cur, 0, out


def corrupt(rng, table, columns):
    rows = [list(r) for r in table]
    for x in columns:
        for u in rng.sample(range(len(rows)), rng.randrange(1, len(rows) + 1)):
            rows[u][x] ^= rng.randrange(1, 1 << M)
    return rows


def plant_repair(rng, word, truth, alpha, beta, x):
    """Rewrite column x of the word so that every lane pair has a nonzero error that the round-1 fold cancels."""
    a = alpha ^ mul(beta, x)
    for u in range(0, len(word), 2):
        e0 = rng.randrange(1, 1 << M)
        word[u][x] = truth[u][x] ^ e0
        word[u + 1][x] = truth[u + 1][x] ^ mul(a, e0)


def run(seed):
    rng = random.Random(seed)
    counts = dict(X1=0, X2=0, X3=0, X4=0, X5=0)
    for _trial in range(6):
        lanes = make_tuple(rng)
        truth = [table_of(lanes)]
        challenges = [(rng.randrange(1, 1 << M), rng.randrange(1, 1 << M)) for _ in range(ELL)]
        for alpha, beta in challenges:
            truth.append(fold_table(truth[-1], alpha, beta))
        bad_cols = rng.sample(range(N), N - A0 - ELL - 2)

        # X1: plain corruption
        word = corrupt(rng, truth[0], bad_cols)
        got, failed_at, path = descend(word, challenges, truth[ELL])
        assert got is not None and got == truth[0], "X1"
        assert all(t == truth[ELL - 1 - k] for k, t in enumerate(path)), "X1 path"
        counts["X1"] += 1

        # X2: one repaired column at round 1
        word2 = [list(r) for r in word]
        x0 = bad_cols[0]
        plant_repair(rng, word2, truth[0], challenges[0][0], challenges[0][1], x0)
        w1 = fold_table(word2, *challenges[0])
        assert all(w1[u][x0] == truth[1][u][x0] for u in range(len(w1))), "repair planted"
        S1 = agreement(truth[1], w1)
        assert x0 in S1 and any(word2[u][x0] != truth[0][u][x0] for u in range(len(word2)))
        got, failed_at, _ = descend(word2, challenges, truth[ELL])
        assert got is not None and got == truth[0], "X2"
        counts["X2"] += 1

        # X5: uniqueness of the near tuple on S1
        cands = near_decode(word2, S1, D, all_candidates=True)
        assert cands and all(c == truth[0] for c in cands), "X5"
        counts["X5"] += 1

        # X4: two repaired columns at round 1: no near tuple
        word4 = [list(r) for r in word2]
        x1 = bad_cols[1]
        plant_repair(rng, word4, truth[0], challenges[0][0], challenges[0][1], x1)
        got, failed_at, _ = descend(word4, challenges, truth[ELL])
        assert got is None and failed_at == 1, "X4"
        counts["X4"] += 1

        # X3: two list members; the descent follows the run
        lanes_b = make_tuple(rng)
        truth_b = [table_of(lanes_b)]
        for alpha, beta in challenges:
            truth_b.append(fold_table(truth_b[-1], alpha, beta))
        cols = list(range(N))
        rng.shuffle(cols)
        half_a = set(cols[: N // 2])
        word3 = [[truth[0][u][x] if x in half_a else truth_b[0][u][x] for x in range(N)] for u in range(1 << ELL)]
        assert len(agreement(truth[0], word3)) >= A0 and len(agreement(truth_b[0], word3)) >= A0
        got_a, _, _ = descend(word3, challenges, truth[ELL])
        got_b, _, _ = descend(word3, challenges, truth_b[ELL])
        assert got_a == truth[0] and got_b == truth_b[0], "X3"
        points = [(rng.randrange(1, 1 << M), rng.randrange(1, 1 << M)) for _ in range(2)]
        assert any(ev_point(th, ze, lanes) != ev_point(th, ze, lanes_b) for th, ze in points), "X3 pinning"
        counts["X3"] += 1
    return counts


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    counts = run(seed)
    print(f"n = {N}, lanes = {1 << ELL}, d = {D}, A0 = {A0}, thresholds {[A0 + j for j in range(ELL + 1)]}")
    print(f"X1 descent returns the committed-for tuple, no repair: {counts['X1']} of {counts['X1']}")
    print(f"X2 one repaired column, descent still returns it: {counts['X2']} of {counts['X2']}")
    print(f"X3 two list members, descent follows the run, point answers differ: {counts['X3']} of {counts['X3']}")
    print(f"X4 two repaired columns, no near tuple, extractor fails at round 1: {counts['X4']} of {counts['X4']}")
    print(f"X5 near tuple unique over all leave-one-out candidates: {counts['X5']} of {counts['X5']}")


if __name__ == "__main__":
    main()
