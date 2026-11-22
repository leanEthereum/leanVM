"""Checks for 06-capacity-codes.md.

1. x has order 2^64 - 1 in K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), so gamma = x is a valid FRS multiplier.
2. Toy version of the "Sidon coset union" domain. GF(32), k = 4 (kappa = 2), n = 16 (rate 1/4). Both domains
   are unions of four cosets of S_2 = span(1, x), so the additive NTT costs the same on both:
     subspace: span(1, x, x^2, x^3)                      (what leanVM uses)
     sidon:    S_2 + {0, x^2, x^3, x^4}                  (coset representatives with no additive relation)
   For every monomial word x^e, count the polynomials of degree < 4 agreeing with it on at least a points.
   Lead's flats lemma: on the subspace domain x^7 has 15 such polynomials at a = 7 = n/2 - 1 (one per hyperplane).
   Checked here: on the sidon domain it has 3 (the pairs {0, c_i}). With --all, over every monomial word, the
   largest list at a >= 7 is 15 on the subspace and 3 on the sidon domain; at a >= 6 both reach 16, which is the
   random-agreement regime at this size (a random word expects C(16,6)/32^2 = 7.8 polynomials there).
   Degree <= 4 (the analysis degree d >= 2^kappa): the word x^8 agrees on 8 points with one polynomial of degree 4
   per affine flat of dimension 3 inside the domain: 30 on the subspace, 6 on the sidon domain.
"""
import sys

def clmul_mod(a, b, mod, bits):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        if a >> bits:
            a ^= mod
        b >>= 1
    return r

# --- 1. order of x in K
MOD64, B64 = (1 << 64) | 0b11011, 64
def pow64(a, e):
    r = 1
    while e:
        if e & 1:
            r = clmul_mod(r, a, MOD64, B64)
        a = clmul_mod(a, a, MOD64, B64)
        e >>= 1
    return r
ORDER = (1 << 64) - 1
PRIMES = [3, 5, 17, 257, 641, 65537, 6700417]
prod = 1
for p in PRIMES:
    prod *= p
assert prod == ORDER
assert pow64(2, ORDER) == 1 and all(pow64(2, ORDER // p) != 1 for p in PRIMES)
print("x has order 2^64 - 1 in K: checked")

# --- 2. toy coset domains over GF(32)
MOD5, B5, Q = 0b100101, 5, 32
MUL = [[clmul_mod(a, b, MOD5, B5) for b in range(Q)] for a in range(Q)]
def power(a, e):
    r = 1
    for _ in range(e):
        r = MUL[r][a]
    return r

K_DIM, N_PTS = 4, 16
DOMAINS = {
    "subspace": [c ^ s for c in (0, 4, 8, 12) for s in range(4)],
    "sidon": [c ^ s for c in (0, 4, 8, 16) for s in range(4)],
}
MASK20 = (1 << 20) - 1
ZERO_FIELDS = bytearray(1 << 20)  # number of zero 5-bit fields in a 20-bit chunk
for v in range(1 << 20):
    ZERO_FIELDS[v] = ((v & 31) == 0) + (((v >> 5) & 31) == 0) + (((v >> 10) & 31) == 0) + ((v >> 15) == 0)

def pack(values):
    r = 0
    for j, v in enumerate(values):
        r |= v << (5 * j)
    return r

def lists(domain, words, min_agree, top=False):
    """For each word (an exponent e, the word x^e): histogram {agreement: count} over all polys of degree < 4,
    or with top=True over all polys of degree exactly 4."""
    col = [[pack([MUL[c][power(x, i)] for x in domain]) for c in range(Q)] for i in range(K_DIM + 1)]
    lo = [col[0][a] ^ col[1][b] for a in range(Q) for b in range(Q)]
    hi = [col[2][a] ^ col[3][b] for a in range(Q) for b in range(Q)]
    if top:
        hi = [h ^ col[4][c] for h in hi for c in range(1, Q)]
    out = {}
    for e in words:
        w = pack([power(x, e) for x in domain])
        hist = {}
        for h in hi:
            hw = h ^ w
            for l in lo:
                z = hw ^ l
                c = ZERO_FIELDS[z & MASK20] + ZERO_FIELDS[(z >> 20) & MASK20] + ZERO_FIELDS[(z >> 40) & MASK20] + ZERO_FIELDS[z >> 60]
                if c >= min_agree:
                    hist[c] = hist.get(c, 0) + 1
        out[e] = hist
    return out

words = range(4, 31) if "--all" in sys.argv else [7]
res = {name: lists(dom, words, 6) for name, dom in DOMAINS.items()}
for e in words:
    for name in DOMAINS:
        h = res[name][e]
        print(f"word x^{e:<2} on {name:<8}: " + ", ".join(f"{h[a]} polys at agreement {a}" for a in sorted(h, reverse=True)) if h else f"word x^{e:<2} on {name:<8}: none at agreement >= 6")
ge = lambda h, a: sum(v for k, v in h.items() if k >= a)
for a in (7, 6):
    print(f"max over these words of the list at agreement >= {a}: " + ", ".join(f"{name} {max(ge(res[name][e], a) for e in words)}" for name in DOMAINS))
assert ge(res["subspace"][7], 7) >= 15 and ge(res["sidon"][7], 7) == 3
for name, dom in DOMAINS.items():
    h = lists(dom, [8], 8, top=True)[8]
    print(f"word x^8 on {name:<8}, polys of degree exactly 4: " + ", ".join(f"{h[a]} at agreement {a}" for a in sorted(h, reverse=True)))
