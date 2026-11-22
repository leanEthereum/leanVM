#!/usr/bin/env python3
"""Note 78, experiment 5(b) for V2: messages that are products for both variable systems.
In characteristic 2 the table of a multilinear polynomial is an element of the group algebra K[F_2^v] (monomial X^e <-> e), a
product of polynomials in disjoint variables is the product in that algebra, and tree 1 of V2(M) reads the image under the
automorphism e -> M e. With V_i = low i bits, U_i = the other bits: for a subgroup S of R = V_i cap M^-1 V_j with
M U_i inside U_j + M S, every message A(X_up) * 1_S * B1 (A arbitrary on U_i, B1 supported on R, 1_S the indicator of S) is
A(X_up) B(X_low) for tree 0 with B = 1_S * B1, and A'(Y_up) B'(Y_low) for tree 1 with B' = 1_{MS} * (B1 o M^-1): a lift at
level i of tree 0 and level j of tree 1 whose common lower factor ranges over a space of dimension |R|/|S|, so it has
|R|/|S| - 1 prescribable common zeros (a plain tree code has 2^i - 1 at level i).
usage: 78_e5_products.py v name...        per matrix: for every level i the largest |R|/|S| with j = i, and with j < i
       78_e5_products.py all4 FILE        every matrix of the GL_4 section of 78_e2_gl_output.txt: MDS against product-free"""
import sys, itertools, importlib.util, os
spec = importlib.util.spec_from_file_location("mat78", os.path.join(os.path.dirname(os.path.abspath(__file__)), "78_mat.py"))
mat = importlib.util.module_from_spec(spec); spec.loader.exec_module(mat)

def apply(M, v, e):
    return sum((bin(M[l] & e).count('1') & 1) << l for l in range(v))
def subspaces(elems):
    """all subgroups of the F_2-space given as a set of ints"""
    elems = sorted(elems); out = {frozenset([0])}
    frontier = [frozenset([0])]
    while frontier:
        nxt = []
        for S in frontier:
            for x in elems:
                if x in S: continue
                T = frozenset(S | {s ^ x for s in S})
                if T not in out: out.add(T); nxt.append(T)
        frontier = nxt
    return out
def span(vecs):
    S = {0}
    for x in vecs:
        if x not in S: S |= {s ^ x for s in S}
    return S
def lift_index(M, v):
    """returns {i: (best |R|/|S| with j = i, best with j < i as (dim, j))}"""
    Minv = mat.inv(M, v); res = {}
    for i in range(1, v):
        Vi = set(range(1 << i)); Ui_basis = [1 << l for l in range(i, v)]
        best_same, best_lower = 1 if False else 0, (0, None)
        for j in range(1, i + 1):
            Vj = set(range(1 << j)); Uj = {u << j for u in range(1 << (v - j))}
            R = {w for w in Vi if apply(M, v, w) in Vj}
            for S in subspaces(R):
                MS = {apply(M, v, s) for s in S}
                target = {u ^ s for u in Uj for s in MS}
                if all(apply(M, v, u) in target for u in Ui_basis):
                    dim = len(R) // len(S)
                    if j == i: best_same = max(best_same, dim)
                    elif dim > best_lower[0]: best_lower = (dim, j)
        res[i] = (best_same, best_lower)
    return res
def main():
    if sys.argv[1] == 'all4':
        import re, collections
        v = 4; data = {}
        for line in open(sys.argv[2]):
            m = re.match(r'^(\d+) (\d+)$', line)
            if m: data[int(m.group(1))] = int(m.group(2))
        tab = collections.Counter(); free_mds = []
        for code, ident in sorted(data.items()):
            M = [(code >> (l * v)) & 15 for l in range(v)]
            li = lift_index(M, v)
            mx = max(max(a, b[0]) for a, b in li.values())
            tab[(ident == 0, mx)] += 1
            if ident == 0 and mx <= 1: free_mds.append((sum(bin(x).count('1') for x in M), code, M))
        print("GL_4: (MDS, largest lower-factor dimension over levels) -> number of matrices")
        for key in sorted(tab): print("  ", key, tab[key])
        free_mds.sort()
        print("MDS matrices with no two-sided product family of lower-factor dimension >= 2: %d; sparsest:" % len(free_mds))
        for ones, code, M in free_mds[:12]:
            low, high, lu = mat.flags(M, v)
            print("   #%d rows %s ones %d lowpres %d highpres %d lu %d" % (code, ' '.join(format(x, '04b') for x in M), ones, low, high, int(lu)))
        return
    v = int(sys.argv[1])
    for e in sys.argv[2:]:
        M = mat.parse(e, v); li = lift_index(M, v)
        print(f"v={v} {e}: " + "; ".join(f"level {i}: same-level lower-factor dim {a} (tree code {1 << i})" + (f", with tree-1 level {b[1]}: {b[0]}" if b[1] else "") for i, (a, b) in li.items()))
main()
