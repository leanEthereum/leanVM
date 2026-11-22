"""Note 86: exact linear algebra over GF(2^64) = F_2[x]/(x^64+x^4+x^3+x+1) for the generic T2 tree code.

Field elements are Python ints in "spread" form (bit i of the element sits at bit 7*i), so that a carry-less
product is one integer product followed by a mask; addition is XOR. Everything here is exact at a random draw
of the twiddles (a lower bound on generic ranks, as in notes 69 to 82).
"""
import random

S = 7
MASK = sum(1 << (S * i) for i in range(127))
LOW = (1 << (S * 64)) - 1
def spread(a):
    r = 0; i = 0
    while a:
        if a & 1: r |= 1 << (S * i)
        a >>= 1; i += 1
    return r
def mul(a, b):
    p = (a * b) & MASK
    h = p >> (S * 64); l = p & LOW
    l ^= h ^ (h << S) ^ (h << (3 * S)) ^ (h << (4 * S))
    h = l >> (S * 64); l &= LOW
    return l ^ h ^ (h << S) ^ (h << (3 * S)) ^ (h << (4 * S))
def inv(a):
    r, e, b = 1, (1 << 64) - 2, a
    while e:
        if e & 1: r = mul(r, b)
        b = mul(b, b); e >>= 1
    return r
def rnd_elt(rnd): return spread(rnd.getrandbits(64))

def rref(M, ncols=None):
    """reduced row echelon form; returns (rows, pivot columns)"""
    M = [row[:] for row in M if any(row)]
    if not M: return [], []
    cols = len(M[0]) if ncols is None else ncols
    piv = []; r = 0
    for c in range(cols):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        iv = inv(M[r][c]); M[r] = [mul(iv, x) if x else 0 for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]; Mr = M[r]; M[i] = [x ^ mul(f, y) if y else x for x, y in zip(M[i], Mr)]
        piv.append(c); r += 1
        if r == len(M): break
    return M[:r], piv
def rank(M): return len(rref(M)[1]) if M else 0
def kernel(M, cols):
    """basis of {x : M x = 0} (right kernel)"""
    R, piv = rref(M) if M else ([], [])
    out = []; ps = set(piv)
    for c in range(cols):
        if c in ps: continue
        x = [0] * cols; x[c] = 1
        for i, pc in enumerate(piv): x[pc] = R[i][c]
        out.append(x)
    return out
def left_kernel(M):
    """basis of {y : y M = 0}"""
    if not M: return []
    T = [list(col) for col in zip(*M)]
    return kernel(T, len(M))
def in_span(R, piv, v):
    """v in the row space given by its rref (R, piv)?"""
    v = v[:]
    for row, pc in zip(R, piv):
        if v[pc]:
            f = v[pc]; v = [x ^ mul(f, y) if y else x for x, y in zip(v, row)]
    return not any(v)
def reduce_mod(R, piv, v):
    v = v[:]
    for row, pc in zip(R, piv):
        if v[pc]:
            f = v[pc]; v = [x ^ mul(f, y) if y else x for x, y in zip(v, row)]
    return v
def dot(a, b):
    s = 0
    for x, y in zip(a, b):
        if x and y: s ^= mul(x, y)
    return s

class Tree:
    """generic T2 tree code with k = 2^v, n = 2^(v+r); node q of height i has twiddle tw[i][q]"""
    def __init__(self, v, r, seed=1):
        rnd = random.Random(seed)
        self.v, self.r = v, r; self.n = 1 << (v + r); self.k = 1 << v
        self.tw = [[rnd_elt(rnd) for q in range(self.n >> i)] for i in range(v)]
    def nodes(self, h): return self.n >> h
    def dim(self, h): return self.k >> h
    def row(self, h, u):
        """row of the node u of height h in the code of the layers >= h (message index bit i-h is layer i)"""
        g = [1]
        for i in range(h, self.v):
            x = self.tw[i][u >> (i - h)]
            g = g + [mul(y, x) for y in g]
        return g
    def rows(self, h): return [self.row(h, u) for u in range(self.nodes(h))]

def tensor(theta, g, L):
    """theta in F_2^L as a bitmask (bit a = member a+1), g a row: theta (x) g in K^L (x) K^K, index a*K+e"""
    K = len(g); out = [0] * (L * K)
    for a in range(L):
        if (theta >> a) & 1: out[a * K:(a + 1) * K] = g
    return out
def tensor_K(nu, g):
    """nu a list of L field elements"""
    out = []
    for c in nu: out += [mul(c, y) if c else 0 for y in g]
    return out

# three members: classes as subspaces of F_2^2: member vectors e_0 = 0, e_1 = 1, e_2 = 2
CLS3 = {'.': [], '01': [1], '02': [2], '12': [3], '012': [1, 2]}
def parse(s): return [t for t in s.replace('|', ' ').split()]
def basis_of(tok):
    """basis (bitmasks) of the binary space of a token: '.', a class like '013', or a list of vectors"""
    if isinstance(tok, (list, tuple)): return list(tok)
    if tok == '.': return []
    mem = [int(c) for c in tok]; e = lambda a: (1 << (a - 1)) if a else 0
    return [e(mem[0]) ^ e(b) for b in mem[1:]]
def pattern_rows(G, pat, L):
    rows = []
    for x, tok in enumerate(pat):
        for th in basis_of(tok): rows.append(tensor(th, G[x], L))
    return rows
def weight(pat): return sum(len(basis_of(t)) for t in pat)
