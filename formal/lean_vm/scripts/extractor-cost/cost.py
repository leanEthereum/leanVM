#!/usr/bin/env python3
"""The knowledge extractor's cost, per shape: a model, not a proof.

  python3 -I cost.py params.csv            the table, every shape
  python3 -I cost.py params.csv --worst    the worst shape per component and the totals

`params.csv` is `params.lean`'s output: the list decoder's parameters at every shape `(μ, R)` as
the statement computes them. Every cost is a count of operations of `K = GF(2^64)` or of 64-bit
words, constants dropped, as `log2`; where the work is per lane it is counted for all `2^6` lanes.
Each formula is read off the code it names (`lean_vm/LeanVM/Protocol/Extraction/Extractor.lean`, CompPoly at the
lakefile's pin), and its derivation is in the comments.

Three tiers:
* tier 0: today's code;
* tier 1 (E1): Roth-Ruckenstein with a linear Taylor shift, binomials by parity and truncated
  substitution (the textbook bound), no final root check, sorted lookups; "as built": E1 as
  implemented (`LeanVM/Protocol/Extraction/Fast/`), the substitution untruncated; "2 as built":
  the approximant-basis interpolation on Karatsuba's products, a model of an earlier build (the
  compiled extractor now multiplies by the additive FFT, its price proved in `lean_vm`:
  `decoderBoundPM`, about `2^94.07` at the worst shape at level 0's earlier, balanced slacks,
  Roth-Ruckenstein dominating: `rrBound`, about `2^87.98` per lane,
  `tests/LeanVMTests/Cost/RrBound.lean`; at the largest slacks the same model gives about
  `2^82.05`);
* tier 2 (E2): tier 1 with a fast interpolation (Chowdhury et al. 2015) in place of
  Lee-O'Sullivan and Mulders-Storjohann.

The terms in `N`, the transcript's permutation queries, are printed as formulas: they are the
adversary's to choose.
"""
import csv
import math
import sys

LANES = 6  # log2 of the 2^6 lanes
LIST = 12  # log2 of the candidates (`candidates_ncard_le`) and the pruning survivors
           # (`pruneUpTo_length_le`)
KECCAK = 12  # log2 of Keccak-f[1600]'s word operations, 24 rounds of about 170


def lg(x):
    return math.log2(x)


def costs(r):
    mu, R, kappa, n, A, m, ell = (int(r[c]) for c in ("mu", "R", "kappa", "n", "A", "m", "ell"))
    k = 2 ** kappa
    q = int(r["vars"])  # the interpolation's unknowns: a bound on Q's coefficients, |Q|
    w = m * A - 1  # Q's (1, k-1)-weighted degree, so its X-degree
    t = {}
    # Interpolation, Lee-O'Sullivan's basis reduced by Mulders-Storjohann
    # (`PolynomialMatrix.muldersStorjohannFastReducerContext`): r^3 d^2 for an r x r basis of
    # degree d, r = ell + 1, d = m n.
    t["interp0"] = LANES + 3 * lg(ell + 1) + 2 * lg(m * n)
    # Fast interpolation (Chowdhury et al.): ell^(omega-1) m^2 n with omega = 3, and up to
    # log^2(m n) more (printed separately).
    t["interp2"] = LANES + 2 * lg(ell) + 2 * lg(m) + lg(n)
    t["interp2log"] = 2 * lg(lg(m * n))
    # E2 as built: the same interpolation (CompPoly's approximant basis) on Karatsuba's products:
    # the products of degree about m n / ell cost (m n / ell)^0.585 more than a quasi-linear
    # one, no log factor (a heuristic: CompPoly's PM-basis is not analysed term by term); the
    # relation matrix's ell m products of degree m n, (m n)^1.585 each.
    t["interpKara"] = max(LANES + 2 * lg(ell) + 2 * lg(m) + lg(n) + 0.585 * lg(m * n / ell),
                          LANES + lg(ell) + lg(m) + 1.585 * lg(m * n))
    # Roth-Ruckenstein as implemented (`substituteYRootPlusXY`): for each of the |Q| terms
    # x^i y^j, j + 1 monomials added one by one to a dense accumulator (`out + monomialXY`), each
    # addition Theta(|Q|): |Q|^2 ell / 2 per substitution; one substitution per depth, k depths
    # per path (`transformedRothRuckensteinRootPrefixesWithFuel`, fuel k); between 1 and ell live
    # paths.
    t["rr0"] = LANES + lg(k) + 2 * lg(q) + lg(ell / 2)
    t["rr0paths"] = lg(ell)
    # ... and a `Nat.choose y t` per monomial, a bignum of about y bits built by y
    # multiplications: about y^2/64 word operations, y <= ell.
    t["binom0"] = LANES + lg(k) + lg(q) + lg(ell / 2) + 2 * lg(ell) - 6
    # Roth-Ruckenstein with the Taylor shift, untruncated (E1 as built, `substituteFast`): for
    # each t <= ell, the sum over y >= t of the Q_y, each of X-degree at most W: ell^2 W / 2 per
    # substitution, k per path, between 1 and ell paths.
    t["rrTaylor"] = LANES + lg(k) + lg(ell * ell * w / 2) + lg(ell)
    # ... and truncated (E1 as built, `prefixesTrunc`): Q modulo X^M, M = k - depth at simple
    # roots, so ell^2 (k - d) / 2 at depth d: ell^2 k^2 / 4 per path (falling back to the exact
    # recursion where a repeated root strips more than one power of X: not counted).
    t["rrTrunc"] = LANES + 2 * lg(ell) + 2 * lg(k) - 2 + lg(ell)
    # Roth-Ruckenstein, textbook (tier 1): O(ell log^2 ell k (n + ell log q)).
    t["rr1"] = LANES + lg(ell) + 2 * lg(lg(ell)) + lg(k) + lg(n + 64 * ell)
    # The final root check (`isRootYDegreeLtBool`, `composeYHorner`): ell Horner steps, each a
    # `mulRaw` iterating over the accumulator (degree up to w + ell k) with a dense addition of
    # that size: ell (w + ell k)^2 per candidate, at most ell candidates per lane.
    t["final0"] = LANES + lg(ell) + lg(ell) + 2 * lg(w + ell * k)
    # The distance filter (`passesCandidateDistance`): a candidate's encoding on the n points,
    # about n k, for at most ell candidates per lane.
    t["filter"] = LANES + lg(ell) + lg(n) + lg(k)
    # Pruning (`pruneUpTo`): at most 2^LIST survivors per lane, each compared with each lane's
    # candidates on n columns: 64 L^2 n.
    t["prune"] = LANES + 2 * LIST + lg(n)
    # Candidate runs: at most 2^LIST stacks, each run for at most `stepCap` <= 2^mu steps, a
    # KECCAK step about 2^KECCAK.
    t["runs"] = LIST + mu + KECCAK
    return t


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    rows = list(csv.DictReader(open(sys.argv[1])))
    table = [(int(r["mu"]), int(r["R"]), costs(r)) for r in rows]
    if "--worst" in sys.argv:
        keys = ["interp0", "interp2", "interpKara", "rr0", "binom0", "rrTaylor", "rrTrunc", "rr1", "final0", "filter",
                "prune", "runs"]
        for key in keys:
            mu, R, t = max(table, key=lambda x: x[2][key])
            print(f"{key:9s} 2^{t[key]:6.1f}  at ({mu}, {R})")
        tier = {
            0: lambda t: max(t["interp0"], t["rr0"] + t["rr0paths"], t["final0"], t["prune"],
                             t["runs"]),
            "1 as built (E1)": lambda t: max(t["interp0"], t["rrTrunc"], t["filter"], t["prune"],
                                             t["runs"]),
            "2 as built (E2)": lambda t: max(t["interpKara"], t["rrTrunc"], t["filter"],
                                             t["prune"], t["runs"]),
            1: lambda t: max(t["interp0"], t["rr1"], t["prune"], t["runs"]),
            2: lambda t: max(t["interp2"] + t["interp2log"], t["rr1"], t["prune"], t["runs"]),
        }
        for i, f in tier.items():
            mu, R, t = max(table, key=lambda x: f(x[2]))
            print(f"tier {i}: C0 = 2^{f(t):.1f} at ({mu}, {R})")
        print("plus, in N: tier 0  136 N^3/6 + 2^14 N^2 + 2^27 N (lookups and paths);"
              " E1 as built  O(N L) expected (hash maps, L = max(64, 8 width) bytes)")
        return
    print("mu  R | interp0 interp2(+log) | rr0 (1..ell paths) binom0 rr1 | final0 filter "
          "prune runs")
    for mu, R, t in table:
        print(f"{mu:2d} {R:2d} | {t['interp0']:6.1f} {t['interp2']:6.1f}(+{t['interp2log']:.1f})"
              f" | {t['rr0']:6.1f}..{t['rr0'] + t['rr0paths']:6.1f} {t['binom0']:6.1f}"
              f" {t['rr1']:5.1f} | {t['final0']:5.1f} {t['filter']:5.1f} {t['prune']:5.1f}"
              f" {t['runs']:5.1f}")


if __name__ == "__main__":
    main()
