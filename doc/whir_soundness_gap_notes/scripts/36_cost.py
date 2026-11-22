#!/usr/bin/env python3
"""Note 36, section 8: multiplication counts of the encoders, relative to today's additive NTT.

Model (an estimate, not a measurement):
  today            kappa/2 multiplications per point and lane (Proposition prop:ntt of Annex D)
  random points    n/k batches of k points, each a remainder tree over a precomputed, transformed
                   subproduct tree. Going from a node of size 2^(j+1) to a child of size 2^j is one middle
                   product: one forward and one inverse additive transform of size 2^(j+1) and 2^(j+1)
                   pointwise products, 2^(j+1) (j+2) multiplications ("low"); twice that if the middle
                   product needs transforms of double size ("high"). Subtrees of 8 points by Horner.
                   For k <= 64 plain Horner (k multiplications a point) is cheaper.
  coset union      cosets of size w = 2^c, random representatives: w multipoint evaluations with k/w
                   coefficients at n/w points, then one size-w transform per coset.
Shares of the levels in committed words are note 08's (mu = 30, rate 1/2). Usage: python3 36_cost.py
"""


def tree_mults_per_point(kappa, high=False):
    """Multiplications per point of a remainder tree for k = 2^kappa points and degree < k."""
    j0 = min(3, kappa)
    per_batch = sum(2 * (j + 2) for j in range(j0, kappa)) * (2 if high else 1) + 2 ** j0  # in units of k
    return min(per_batch, 2 ** kappa)


def ratio_random(kappa, high=False):
    return tree_mults_per_point(kappa, high) / (kappa / 2)


def ratio_coset(kappa, c, high=False):
    kp = kappa - c
    return (tree_mults_per_point(kp, high) + c / 2) / (kappa / 2)


def main():
    levels = [(0, 24, 1.0), (1, 20, 1 / 4), (2, 16, 1 / 8), (3, 12, 1 / 16), (4, 8, 1 / 32), (5, 4, 1 / 64)]
    print("| level | kappa | share of level-0 words | random points, x own NTT (low to high) | in level-0 NTTs | cosets of 4 | cosets of 16 |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for i, kappa, share in levels:
        lo, hi = ratio_random(kappa), ratio_random(kappa, True)
        c4 = ratio_coset(kappa, 2) if kappa > 2 else float("nan")
        c16 = ratio_coset(kappa, 4) if kappa > 4 else float("nan")
        print(f"| {i} | {kappa} | {share:.4f} | {lo:.0f} to {hi:.0f} | {lo * share:.2f} to {hi * share:.2f} | {c4:.0f} | {c16:.0f} |")
    print()
    print("precomputed tree, kappa field elements per point (read once per lane):")
    for i, kappa, share in levels:
        n = 2 ** (25 - i)
        print(f"  level {i}: {kappa * n * 8 / 2**30:.2f} GiB for points in K")


if __name__ == "__main__":
    main()
