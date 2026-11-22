# 30_lib: small exact linear algebra over GF(2^64) for patterns of multiplicity vectors on a generic subspace.
# A generic N-dimensional subspace is simulated by a random basis in GF(2^64) (x^64 + x^4 + x^3 + x + 1).
# A nonzero determinant for the random basis proves a nonzero determinant for the generic one; a zero one is
# evidence (error probability about degree / 2^64), not proof.
import random

MOD = (1 << 64) | 0x1b

def gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
    for i in range(r.bit_length() - 1, 63, -1):
        if r >> i & 1:
            r ^= MOD << (i - 64)
    return r

def gpow(a, e):
    r = 1
    while e:
        if e & 1:
            r = gmul(r, a)
        a = gmul(a, a)
        e >>= 1
    return r

def ginv(a):
    return gpow(a, (1 << 64) - 2)

def subspace(N, rng):
    b = [rng.getrandbits(64) for _ in range(N)]
    pts = []
    for p in range(1 << N):
        x = 0
        for i in range(N):
            if p >> i & 1:
                x ^= b[i]
        pts.append(x)
    return pts

def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] ^= gmul(x, y)
    return r

def ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a

def padd(a, b):
    n = max(len(a), len(b))
    return ptrim([(a[i] if i < len(a) else 0) ^ (b[i] if i < len(b) else 0) for i in range(n)])

def pdivmod(a, b):
    a = ptrim(a); b = ptrim(b)
    q = [0] * max(1, len(a) - len(b) + 1)
    inv = ginv(b[-1])
    a = list(a)
    for i in range(len(a) - 1, len(b) - 2, -1):
        if i < len(a) and a[i]:
            f = gmul(a[i], inv)
            q[i - len(b) + 1] = f
            for j, y in enumerate(b):
                a[i - len(b) + 1 + j] ^= gmul(f, y)
    return ptrim(q), ptrim(a)

def pgcd(a, b):
    a = ptrim(a); b = ptrim(b)
    while b:
        _, r = pdivmod(a, b)
        a, b = b, r
    return a

def peval(a, x):
    v = 0
    for c in reversed(a):
        v = gmul(v, x) ^ c
    return v

def locator(pts, m):
    z = [1]
    for p, mult in enumerate(m):
        for _ in range(mult):
            z = pmul(z, [pts[p], 1])
    return z

def kernel(rows_cols):
    """columns given as list of vectors (lists of equal length nr); returns a basis of the kernel (coefficient vectors)."""
    cols = rows_cols
    nc = len(cols)
    if nc == 0:
        return []
    nr = len(cols[0])
    A = [[cols[c][r] for c in range(nc)] for r in range(nr)]
    piv = []
    rank = 0
    for c in range(nc):
        r = rank
        while r < nr and not A[r][c]:
            r += 1
        if r == nr:
            continue
        A[r], A[rank] = A[rank], A[r]
        inv = ginv(A[rank][c])
        A[rank] = [gmul(inv, x) for x in A[rank]]
        for rr in range(nr):
            if rr != rank and A[rr][c]:
                f = A[rr][c]
                A[rr] = [x ^ gmul(f, y) for x, y in zip(A[rr], A[rank])]
        piv.append(c)
        rank += 1
        if rank == nr:
            break
    free = [c for c in range(nc) if c not in piv]
    basis = []
    for fcol in free:
        v = [0] * nc
        v[fcol] = 1
        for r, pc in enumerate(piv):
            v[pc] = A[r][fcol]
        basis.append(v)
    return basis

def pattern_kernel(pts, ms, K, shifts=None, infs=None):
    """ms: list of multiplicity vectors on pts. Space i: Z^{m_i} X^{shift_i} F[X]_{< K - |m_i| - shift_i - inf_i}
    (shift_i: extra multiplicity at 0, inf_i: multiplicity at infinity).
    Returns (kernel basis, layout) of the map (h_i) -> sum Z^{m_i} X^{s_i} h_i into F[X]_{<K}."""
    cols = []
    layout = []
    for i, m in enumerate(ms):
        z = locator(pts, m)
        s = shifts[i] if shifts else 0
        d = len(z) - 1 + s
        for e in range(K - d - (infs[i] if infs else 0)):
            v = [0] * K
            for l, c in enumerate(z):
                v[s + e + l] = c
            cols.append(v)
            layout.append((i, e))
    return kernel(cols), layout

def quo(p, a):
    b = (a & -a).bit_length() - 1
    if p >> b & 1:
        p ^= a
    return (p & ((1 << b) - 1)) | ((p >> (b + 1)) << b)

def push(m, a):
    out = [0] * (len(m) // 2)
    for p, v in enumerate(m):
        out[quo(p, a)] += v
    return out

def restrict(m, f, c):
    """restriction of a multiplicity vector on F_2^N to the affine hyperplane {parity(p & f) = c}; returns (vector on F_2^(N-1), mass sent to infinity)."""
    b = (f & -f).bit_length() - 1
    p0 = (1 << b) if c else 0
    out = [0] * (len(m) // 2)
    inf = 0
    for p, v in enumerate(m):
        if bin(p & f).count('1') & 1 != c:
            inf += v
        else:
            y = p ^ p0
            out[(y & ((1 << b) - 1)) | ((y >> (b + 1)) << b)] += v
    return out, inf
