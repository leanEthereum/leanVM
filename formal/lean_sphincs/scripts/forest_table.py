#!/usr/bin/env python3
"""The codeword table of the forest (`lut`, Sphincs/Scheme.lean) and the tables computed from it.

Usage (from formal/lean_sphincs):
    python3 scripts/forest_table.py info     # composition of the table, f(1..6), digit counts
    python3 scripts/forest_table.py check    # the Lean sources hold exactly the tables computed here
    python3 scripts/forest_table.py write    # rewrite the literals in Scheme.lean, H0FTab.lean, H0PTab.lean, H0NTab.lean

CODES is the table: entry `t` (the 8-bit digest field) is the codeword `d ∈ {0..4}^6`, digit sum 5,
written as the base-5 number with `d_0` the most significant digit. The table is a rule (`rule_codes`):
the codewords sorted by decreasing sum of squared digits, then lexicographically, entry `t` being
codeword number `t mod 214`. `scripts/forest_certificates.py` imports this module.

The tables mirror the Lean definitions exactly (Fractions):
  fTab, f2Tab    H0Tables.lean (`sumTL … KT DK`, `sumTL … KT DK2`), `u ≤ 40`
  P1tab, P2tab   H0MomCert.lean (`P1Q`, `P2Q`), `n ≤ 150`
  PHtab          H0NTab.lean (`PHQ`), `n ≤ 150`
"""

from fractions import Fraction as Fr
from math import comb
import itertools, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

def rule_codes():
    """The 246 codewords sorted by decreasing sum of squared digits, then lexicographically; entry `t` is
    codeword number `t mod 214`."""
    words = [w for w in itertools.product(range(5), repeat=6) if sum(w) == 5]
    words.sort(key=lambda w: (-sum(d * d for d in w), w))
    return [sum(d * 5 ** (5 - i) for i, d in enumerate(words[t % 214])) for t in range(256)]


CODES = rule_codes()

D = 6        # chains of a forest WOTS key
UMAX = 40    # fTab, f2Tab
NMAX = 150   # P1tab, P2tab, PHtab


def digits(code):
    return tuple(code // 5 ** (D - 1 - i) % 5 for i in range(D))


def table(codes=CODES):
    return [digits(c) for c in codes]


def validate(codes=CODES):
    assert len(codes) == 256
    for w in table(codes):
        assert all(0 <= d <= 4 for d in w) and sum(w) == 5
    assert all(sum(d * 5 ** (D - 1 - i) for i, d in enumerate(digits(c))) == c for c in codes)


# ---------------- the codeword-level numerators (H0Tables.lean) ----------------

def f_tabs(codes=CODES, U=UMAX):
    """fTab[u] = sum_m K(m)^u (Delta* K)(m), f2Tab[u] = sum_m K(m)^u (Delta* K^2)(m), K(m) = #{w : lut w <= m}."""
    grid = list(itertools.product(range(5), repeat=D))
    K = dict.fromkeys(grid, 0)
    for w in table(codes):
        K[w] += 1
    for ax in range(D):                       # prefix sums along each axis (cumT)
        for m in grid:
            if m[ax] > 0:
                K[m] += K[m[:ax] + (m[ax] - 1,) + m[ax + 1:]]
    def delta(T):                             # h(y) - h(y + 1) along each axis, 0 beyond the grid (deltaT)
        T = dict(T)
        for ax in range(D):
            for m in grid:                    # increasing order: m + e_ax is still the old value
                if m[ax] < 4:
                    T[m] -= T[m[:ax] + (m[ax] + 1,) + m[ax + 1:]]
        return T
    DK = delta(K)
    DK2 = delta({m: k * k for m, k in K.items()})
    f = [sum(K[m] ** u * DK[m] for m in grid) for u in range(U + 1)]
    f2 = [sum(K[m] ** u * DK2[m] for m in grid) for u in range(U + 1)]
    return f, f2


# ---------------- the per-tree moments (H0MomCert.lean, H0NTab.lean) ----------------

def rup(x, P):
    return Fr(-((-x.numerator * 2 ** P) // x.denominator), 2 ** P)


def moment_tabs(f, f2, N=NMAX, U=UMAX):
    def fQ(u): return Fr(f[u], 256 ** (u + 1)) if u <= U else Fr(1)
    def f2Q(u): return Fr(f2[u], 256 ** (u + 2)) if u <= U else Fr(1)
    def binQ(n, i, a, b): return comb(n, i) * a ** i * b ** (n - i)
    fq = [fQ(u) for u in range(N + 1)]
    f2q = [f2Q(u) for u in range(N + 1)]
    e8, s8, t8 = Fr(1, 8), Fr(7, 8), Fr(6, 8)
    e16, s16, t16 = Fr(1, 16), Fr(15, 16), Fr(14, 16)
    mu = [rup(sum(binQ(i, u, e8, s8) * fq[u] for u in range(i + 1)), 128) for i in range(N + 1)]
    h = [rup(sum(comb(s, u) * fq[u] * fq[s - u] for u in range(s + 1)), 128) for s in range(N + 1)]
    nu = [rup(e8 * sum(binQ(i, u, e8, s8) * f2q[u] for u in range(i + 1)) +
              s8 * sum(binQ(i, s, e8, t8) * h[s] for s in range(i + 1)), 128) for i in range(N + 1)]
    mu2 = [x * x for x in mu]
    g = [rup(sum(comb(s, i) * mu2[i] * mu2[s - i] for i in range(s + 1)), 128) for s in range(N + 1)]
    nu2 = [x * x for x in nu]
    P1 = [rup(sum(binQ(n, i, e16, s16) * mu2[i] for i in range(n + 1)), 128) for n in range(N + 1)]
    P2 = [rup(e16 * sum(binQ(n, i, e16, s16) * nu2[i] for i in range(n + 1)) +
              s16 * sum(binQ(n, s, e16, t16) * g[s] for s in range(n + 1)), 128) for n in range(N + 1)]
    PH = [rup(sum(binQ(n, i, e16, s16) * mu[i] for i in range(n + 1)), 128) for n in range(N + 1)]
    return P1, P2, PH


def lit_counts(codes=CODES):
    """codewords with digit i at least one (BridgeRevealRate.litCount)"""
    return [sum(1 for w in table(codes) if w[i] >= 1) for i in range(D)]


LIT = max(lit_counts())     # the constant of the reveal rate (litCount_le_all)

# ---------------- Lean literals ----------------

def q(x):
    x = Fr(x)
    return str(x.numerator) if x.denominator == 1 else '%d / %d' % (x.numerator, x.denominator)


def lean_codes(codes=CODES):
    rows = [', '.join(str(c) for c in codes[i:i + 16]) for i in range(0, len(codes), 16)]
    return '[' + ',\n   '.join(rows) + ']'


def lean_ints(xs):
    return '[\n    ' + ', '.join(str(x) for x in xs) + ']'


def lean_rats(xs):
    return '[\n    ' + ',\n    '.join(q(x) for x in xs) + ']'


FILES = {
    'codewordCodes': ('Scheme.lean', 'def codewordCodes : List Nat :=\n  '),
    'fTab': ('H0FTab.lean', 'def fTab : List ℤ := '),
    'f2Tab': ('H0FTab.lean', 'def f2Tab : List ℤ := '),
    'P1tab': ('H0PTab.lean', 'def P1tab : List ℚ := '),
    'P2tab': ('H0PTab.lean', 'def P2tab : List ℚ := '),
    'PHtab': ('H0NTab.lean', 'def PHtab : List ℚ := '),
}


def literals(codes=CODES):
    validate(codes)
    f, f2 = f_tabs(codes)
    P1, P2, PH = moment_tabs(f, f2)
    return {'codewordCodes': lean_codes(codes), 'fTab': lean_ints(f), 'f2Tab': lean_ints(f2),
            'P1tab': lean_rats(P1), 'P2tab': lean_rats(P2), 'PHtab': lean_rats(PH)}


def span(src, head):
    i = src.index(head) + len(head)
    assert src[i] == '['
    return i, src.index(']', i) + 1


def parse_list(src, head):
    i, j = span(src, head)
    out = []
    for item in src[i + 1:j - 1].split(','):
        item = item.strip()
        if '/' in item:
            a, b = item.split('/')
            out.append(Fr(int(a.strip()), int(b.strip())))
        elif item:
            out.append(Fr(int(item)))
    return out


def lean_path(name):
    return os.path.join(ROOT, 'Sphincs', FILES[name][0])


def sync(write):
    lits = literals()
    ok = True
    for name, (fn, head) in FILES.items():
        path = lean_path(name)
        src = open(path).read()
        i, j = span(src, head)
        same = parse_list(src, head) == parse_list(head + lits[name], head)
        print('%-14s %-14s %s' % (name, fn, 'ok' if same else ('rewritten' if write else 'DIFFERS')))
        if not same:
            ok = False
            if write:
                open(path, 'w').write(src[:i] + lits[name] + src[j:])
    return ok


def info():
    validate()
    T = table()
    from collections import Counter
    mult = Counter(T)
    pats = Counter()
    for w, m in mult.items():
        pats[(tuple(sorted((d for d in w if d), reverse=True)), m)] += 1
    print('256 entries, %d distinct codewords, %d of them twice' % (len(mult), sum(1 for m in mult.values() if m == 2)))
    for (p, m), n in sorted(pats.items(), reverse=True):
        print('  digits %-16s %2d codewords x%d' % (p, n, m))
    f, f2 = f_tabs()
    print('f(1..6)  =', ' '.join('%.6f' % (f[u] / 256.0 ** (u + 1)) for u in range(1, 7)))
    print('f2(1..6) =', ' '.join('%.6f' % (f2[u] / 256.0 ** (u + 2)) for u in range(1, 7)))
    print('codewords with digit i >= 1:', lit_counts(), ' max', LIT)


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'info'
    if cmd == 'info':
        info()
    elif cmd == 'check':
        sys.exit(0 if sync(False) else 1)
    elif cmd == 'write':
        sync(True)
    else:
        sys.exit(__doc__)
