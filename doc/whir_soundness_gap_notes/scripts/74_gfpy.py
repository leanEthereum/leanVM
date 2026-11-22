"""Note 74: GF(2^64) = F_2[x]/(x^64+x^4+x^3+x+1) and small exact linear algebra, for exploring single instances."""
import random
MOD = (1 << 64) | 0b11011
def mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> 64: a ^= MOD
    return r
def inv(a):
    r, e, b = 1, (1 << 64) - 2, a
    while e:
        if e & 1: r = mul(r, b)
        b = mul(b, b); e >>= 1
    return r
def rref(M):
    """returns (reduced rows, pivot columns)"""
    M = [row[:] for row in M]; piv = []; r = 0
    cols = len(M[0]) if M else 0
    for c in range(cols):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        iv = inv(M[r][c]); M[r] = [mul(iv, x) for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [x ^ mul(f, y) for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
        if r == len(M): break
    return M[:r], piv
def rank(M): return len(rref(M)[1]) if M else 0
def kernel(M, cols):
    """basis of {x : M x = 0}"""
    R, piv = rref(M) if M else ([], [])
    out = []
    for c in range(cols):
        if c in piv: continue
        x = [0] * cols; x[c] = 1
        for i, pc in enumerate(piv): x[pc] = R[i][c]
        out.append(x)
    return out
def rand(rnd): return rnd.getrandbits(64)
