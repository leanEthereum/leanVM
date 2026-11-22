"""Researcher 05: the exact common-top list of the word X^16 L_W at n = 32, rate 1/2, agreement 20 = 5n/8.

Counts, by meet in the middle over the two halves of D_5 inside GF(2^16), all 20-subsets S of D_5 whose locator agrees
with X^16 L_W in every coefficient of degree > 16 (that is e_1, e_2, e_3 of S prescribed), and compares with the
class F_W of 05_check_five_eighths.py (1400 members). For orientation it also counts the sets of size 19, 21 and 22
with the top of X^(T-4) L_W.
Run: python3 05_exact_list_n32.py   (a few seconds)
"""
import sys
from collections import defaultdict

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import importlib

gfm = importlib.import_module("05_gf")
F = gfm.GF(16)
mul = F.mul


def subset_table(points, jmax):
    """For every subset of `points`: (size, e_1..e_jmax)."""
    tab = [(0,) + (0,) * jmax]
    for s in points:
        new = []
        for t in tab:
            e = (1,) + t[1:]
            ne = [t[0] + 1]
            for j in range(1, jmax + 1):
                ne.append(e[j] ^ mul(s, e[j - 1]))
            new.append(tuple(ne))
        tab += new
    return tab


def count(T, target):
    """Number of T-subsets S of D_5 with (e_1..e_j)(S) = target."""
    j = len(target)
    A = subset_table(list(range(16)), j)
    B = subset_table(list(range(16, 32)), j)
    idx = defaultdict(int)
    for t in A:
        idx[t] += 1
    total = 0
    for b in B:
        sb = b[0]
        if sb > T or T - sb > 16:
            continue
        # solve e_k(S) = sum_{i+l=k} a_i b_l for a_k, k = 1..j
        a = [1]
        eb = (1,) + b[1:]
        for k in range(1, j + 1):
            v = target[k - 1]
            for i in range(0, k):
                v ^= mul(a[i], eb[k - i])
            a.append(v)
        total += idx.get((T - sb,) + tuple(a[1:]), 0)
    return total


if __name__ == "__main__":
    LW = F.subspace_poly([1, 2])  # W = span(1, x), codimension 3 in D_5
    cW, cW1 = LW[1], LW[0]
    # X^16 L_W = X^20 + cW X^18 + cW1 X^17: e_1 = 0, e_2 = cW, e_3 = cW1
    print("T=20, top of X^16 L_W (e1,e2,e3): exact list =", count(20, (0, cW, cW1)), "(class F_W: 1400)")
    # same family of tops one step further: T = 21 needs e_1..e_4, T = 22 needs e_1..e_5; try the tops of
    # X^(T-4) L_W (the natural continuations) to see how the list collapses
    print("T=21, top of X^17 L_W (e1..e4 = 0,cW,cW1,0): exact list =", count(21, (0, cW, cW1, 0)))
    print("T=22, top of X^18 L_W (e1..e5): exact list =", count(22, (0, cW, cW1, 0, 0)))
    print("T=19, top of X^15 L_W (e1,e2 = 0,cW): exact list =", count(19, (0, cW)))
