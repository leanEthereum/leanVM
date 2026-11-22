#!/usr/bin/python3
# Referee 80, item 3: the combinatorics of note 76's Corollary 4.2 for three members (L = 2) and a cross-tree partner map.
# A plain pattern is a profile: in each tree, numbers of leaves of type light (at most one member), a, b, c (one pair), F (all three).
# For a bijection mu between the trees: S_mu = sum dim(Psi_x + Psi_mu(x)) (Corollary 4.2: rank >= S_mu), ov_mu = sum dim(Psi_x cap Psi_mu(x)).
# For a cross-tree permutation pi the window interior of Psi has weight ov_mu0 + ov_mu1 <= 2 ov_max.
# Checks, for every profile with the MDS constraints f <= k - 2, f + n_lambda <= k - 1:
#   (A) if S_max <= 2k - 1 (the pattern can have a nonzero solution) then 2 ov_max <= 2k - 2          (Proposition R3)
#   (B) if S_max <= 2k - 1 then 2 ov_max <= S_max                                                     (interior inequality, marked part)
import itertools, sys
import numpy as np
from scipy.optimize import linear_sum_assignment

TYPES = ["0", "a", "b", "c", "F"]
DIM = {"0": 0, "a": 1, "b": 1, "c": 1, "F": 2}
def sumdim(s, t):
    if s == "0": return DIM[t]
    if t == "0": return DIM[s]
    if s == "F" or t == "F": return 2
    return 1 if s == t else 2
def ovl(s, t): return DIM[s] + DIM[t] - sumdim(s, t)

def profiles(k):
    for c in itertools.combinations_with_replacement(range(5), k):
        yield tuple(TYPES[i] for i in c)

def best(p0, p1, fn):
    W = np.array([[fn(s, t) for t in p1] for s in p0])
    r, c = linear_sum_assignment(-W)
    return int(W[r, c].sum())

def run(k):
    tot = adm = failA = failB = 0
    worstA = worstB = None
    profs = list(profiles(k))
    for p0 in profs:
        for p1 in profs:
            if p1 < p0: continue  # symmetric in the two trees
            f = p0.count("F") + p1.count("F")
            if f > k - 2: continue
            if any(f + p0.count(l) + p1.count(l) > k - 1 for l in "abc"): continue
            tot += 1
            smax = best(p0, p1, sumdim)
            if smax > 2 * k - 1: continue
            adm += 1
            ovmax = best(p0, p1, ovl)
            if 2 * ovmax > 2 * k - 2:
                failA += 1; worstA = worstA or (p0, p1, smax, ovmax)
            if 2 * ovmax > smax:
                failB += 1; worstB = worstB or (p0, p1, smax, ovmax)
    print(f"k={k}: {tot} profiles with the MDS constraints, {adm} with S_max <= 2k-1; (A) fails {failA}; (B) fails {failB}")
    if worstA: print("   first failure of (A):", worstA)
    if worstB: print("   first failure of (B): T0=%s T1=%s S_max=%d ov_max=%d" % ("".join(worstB[0]), "".join(worstB[1]), worstB[2], worstB[3]))

if __name__ == "__main__":
    for k in [int(a) for a in sys.argv[1:]] or [2, 3, 4, 5, 6]:
        run(k)

# (C) the min-loss formula behind (B): 2k - S_max = max(0, l - f, l0 - f1, l1 - f0, max_lambda (l + n_lambda - k)) for EVERY profile
# (no MDS constraint needed), and the four covers bounding ov_max: k - l0 + f1, k - l1 + f0, f + m/2.
def run_formula(k, constrained):
    bad = tot = badcov = 0; first = None
    profs = list(profiles(k))
    for p0 in profs:
        for p1 in profs:
            if p1 < p0: continue
            l0, l1, f0, f1 = p0.count("0"), p1.count("0"), p0.count("F"), p1.count("F")
            nl = {c: p0.count(c) + p1.count(c) for c in "abc"}
            if constrained and (f0 + f1 > k - 2 or any(f0 + f1 + nl[c] > k - 1 for c in "abc")): continue
            tot += 1
            loss = 2 * k - best(p0, p1, sumdim)
            form = max(0, l0 + l1 - f0 - f1, l0 - f1, l1 - f0, max(l0 + l1 + nl[c] - k for c in "abc"))
            if loss != form:
                bad += 1; first = first or ("".join(p0), "".join(p1), loss, form)
            ovmax = best(p0, p1, ovl)
            m = sum(nl.values())
            if 2 * ovmax > min(2 * (k - l0 + f1), 2 * (k - l1 + f0), 2 * (f0 + f1) + m): badcov += 1
    print(f"k={k} ({'MDS constraints' if constrained else 'all profiles'}): {tot} profiles, min-loss formula wrong in {bad}, cover bounds on ov_max violated in {badcov}", first or "")

if __name__ == "__main__":
    for k in [2, 3, 4, 5, 6]:
        run_formula(k, False)

# (D) proof of the min-loss formula for every k: the minimum loss of a bijection is a transportation problem on the 5 x 5 types;
# by LP duality and integrality it is the maximum, over the vertices (a, b) of {a_s + b_t <= loss(s, t)} modulo (a + c, b - c),
# of sum_s a_s c0_s + sum_t b_t c1_t. The vertices do not depend on k: enumerate them (a_0 = 0, b = min_s(loss - a), a = min_t(loss - b),
# tight graph connected) and compare with the five kinds of forms 0, l - f, l0 - f1, l1 - f0, l + n_lambda - k.
def dual_vertices(types, loss):
    n = len(types); verts = set()
    for rest in itertools.product(range(-6, 7), repeat=n - 1):
        a = (0,) + rest
        b = tuple(min(loss(types[s], types[t]) - a[s] for s in range(n)) for t in range(n))
        if any(a[s] != min(loss(types[s], types[t]) - b[t] for t in range(n)) for s in range(n)): continue
        # connectivity of the tight graph on 2n nodes
        adj = {i: set() for i in range(2 * n)}
        for s in range(n):
            for t in range(n):
                if a[s] + b[t] == loss(types[s], types[t]): adj[s].add(n + t); adj[n + t].add(s)
        seen = {0}; stack = [0]
        while stack:
            u = stack.pop()
            for w_ in adj[u]:
                if w_ not in seen: seen.add(w_); stack.append(w_)
        if len(seen) == 2 * n: verts.add((a, b))
    return verts

def named_forms(types):
    n = len(types); lines = [t for t in types if t not in ("0", "F")]
    def norm(a, b): return (tuple(x - a[0] for x in a), tuple(x + a[0] for x in b))
    forms = {}
    z = [0] * n
    def vec(**kw): return [kw.get(t, 0) for t in types]
    forms["0"] = norm(z, z)
    forms["l - f"] = norm([1 if t == "0" else -1 if t == "F" else 0 for t in types], [1 if t == "0" else -1 if t == "F" else 0 for t in types])
    forms["l0 - f1"] = norm([1 if t == "0" else 0 for t in types], [-1 if t == "F" else 0 for t in types])
    forms["l1 - f0"] = norm([-1 if t == "F" else 0 for t in types], [1 if t == "0" else 0 for t in types])
    for lam in lines:
        forms[f"l + n_{lam} - k"] = norm([1 if t in ("0", lam) else 0 for t in types], [0 if t in ("0", lam) else -1 for t in types])
    return forms

if __name__ == "__main__":
    for types in (TYPES, ["0", "a", "b", "c", "d", "F"]):
        def loss(s, t):
            if s == "0": return 2 - (0 if t == "0" else 2 if t == "F" else 1)
            if t == "0": return 2 - (2 if s == "F" else 1)
            if s == "F" or t == "F": return 0
            return 1 if s == t else 0
        V = dual_vertices(types, loss); F = named_forms(types)
        names = {v: nme for nme, v in F.items()}
        unknown = [v for v in V if v not in names]
        print(f"types {''.join(types)}: {len(V)} dual vertices:", sorted(names[v] for v in V if v in names), "; not in the list:", unknown)
