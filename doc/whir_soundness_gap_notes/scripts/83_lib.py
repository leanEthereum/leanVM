"""Note 83: GF(2^64) helpers (through 83_bin/libgf83.dylib), the generic tree code T2, incidence systems of patterns.
Conventions of note 69: leaf j of n = 2k leaves, layer 0 = bottom, row[e] = prod_{i : e_i = 1} t_i(j >> i); tree 0 is the
leaves 0..k-1. A pattern is a list cls[x] of bitmasks of members; rows (e_l - e_l0) (x) g_x with member 0 the zero codeword."""
import ctypes, os, random
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
_lib = ctypes.CDLL(os.path.join(here, "83_bin", "libgf83.dylib"))
_u64p = ctypes.POINTER(ctypes.c_uint64)
_lib.g83_mul.restype = ctypes.c_uint64; _lib.g83_mul.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
_lib.g83_inv.restype = ctypes.c_uint64; _lib.g83_inv.argtypes = [ctypes.c_uint64]
_lib.g83_rank.restype = ctypes.c_int; _lib.g83_rank.argtypes = [_u64p, ctypes.c_int, ctypes.c_int]
_lib.g83_kernel.restype = ctypes.c_int; _lib.g83_kernel.argtypes = [_u64p, ctypes.c_int, ctypes.c_int, _u64p]
_lib.g83_matmul.restype = None; _lib.g83_matmul.argtypes = [_u64p, _u64p, ctypes.c_int, ctypes.c_int, ctypes.c_int, _u64p]
def mul(a, b): return _lib.g83_mul(a, b)
def inv(a): return _lib.g83_inv(a)
def _arr(M):
    A = np.ascontiguousarray(np.array(M, dtype=np.uint64)); return A
def rank(M, cols=None):
    A = _arr(M)
    if A.size == 0: return 0
    if A.ndim == 1: A = A.reshape(1, -1)
    return _lib.g83_rank(A.ctypes.data_as(_u64p), A.shape[0], A.shape[1])
def kernel(M, cols):
    """basis (as a numpy array, one vector a row) of {x : M x = 0}"""
    A = _arr(M)
    if A.size == 0: return np.eye(cols, dtype=np.uint64)
    if A.ndim == 1: A = A.reshape(1, -1)
    K = np.zeros((cols, cols), dtype=np.uint64)
    d = _lib.g83_kernel(A.ctypes.data_as(_u64p), A.shape[0], A.shape[1], K.ctypes.data_as(_u64p))
    return K[:d].copy()
def matmul(A, B):
    A = _arr(A); B = _arr(B)
    if A.ndim == 1: A = A.reshape(1, -1)
    if B.ndim == 1: B = B.reshape(-1, 1)
    C = np.zeros((A.shape[0], B.shape[1]), dtype=np.uint64)
    _lib.g83_matmul(A.ctypes.data_as(_u64p), B.ctypes.data_as(_u64p), A.shape[0], A.shape[1], B.shape[1], C.ctypes.data_as(_u64p))
    return C
def make_tw(v, rnd):
    """twiddles tw[i][node], node = leaf >> i, for n = 2^(v+1) leaves; T2: siblings distinct"""
    n = 2 << v; tw = []
    for i in range(v):
        cnt = n >> i; row = []
        for q in range(0, cnt, 2):
            a = rnd.getrandbits(64); b = rnd.getrandbits(64)
            while b == a: b = rnd.getrandbits(64)
            row += [a, b]
        tw.append(row)
    return tw
def gen(tw, v):
    n = 2 << v; k = 1 << v; G = np.zeros((n, k), dtype=np.uint64)
    for j in range(n):
        row = [1] * k
        for i in range(v):
            x = tw[i][j >> i]; h = 1 << i
            for e in range(h): row[h + e] = mul(row[e], x)
        G[j] = row
    return G
def top_tw(tw):
    """twiddles of the code one layer up (drop the bottom layer)"""
    return tw[1:]
def rows_of(G, k, t, cls):
    """incidence rows of a pattern: for every leaf and every member l of the class other than its least member l0"""
    L = t - 1; rows = []
    for x, C in enumerate(cls):
        mem = [l for l in range(t) if (C >> l) & 1]
        for l in mem[1:]:
            r = np.zeros(L * k, dtype=np.uint64); l0 = mem[0]
            if l >= 1: r[(l - 1) * k:l * k] = G[x]
            if l0 >= 1: r[(l0 - 1) * k:l0 * k] = G[x]
            rows.append(r)
    return rows
def rows_of_partition(G, k, t, parts):
    """parts[x] = list of bitmasks (classes of a partition; singletons may be omitted)"""
    rows = []
    for x, P in enumerate(parts):
        for C in P:
            cl = [0] * len(parts); cl[x] = C
            rows += rows_of(G, k, t, cl)
    return rows
def random_point(ker, rnd):
    pt = np.zeros(ker.shape[1], dtype=np.uint64)
    for vct in ker:
        c = rnd.getrandbits(64)
        pt ^= np.array([mul(c, int(x)) for x in vct], dtype=np.uint64)
    return pt
def codewords(G, k, t, pt):
    """codewords of the members (member 0 is zero) for a kernel point pt in K^{L k}"""
    n = G.shape[0]; cw = np.zeros((t, n), dtype=np.uint64)
    for l in range(1, t):
        cw[l] = matmul(G, pt[(l - 1) * k:l * k].reshape(-1, 1)).reshape(-1)
    return cw
def partition_at(values):
    """classes (bitmasks, size >= 2) of the partition of members by value"""
    d = {}
    for l, val in enumerate(values): d.setdefault(int(val), 0); d[int(val)] |= 1 << l
    return sorted(c for c in d.values() if bin(c).count("1") >= 2)
def classes_from_masks(masks, n):
    return [sum(1 << l for l, m in enumerate(masks) if not (m >> x) & 1) for x in range(n)]
def bits(c): return [l for l in range(64) if (c >> l) & 1]
