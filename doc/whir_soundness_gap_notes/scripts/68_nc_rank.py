# Characteristic 2 version over GF(2^16): scalar twiddles (d = 1) against matrix twiddles (d = 2, 3).
import random, sys
POLY = 0x1100B; Q = 1 << 16
EXP = [0] * (2 * Q); LOG = [0] * Q
x = 1
for i in range(Q - 1):
    EXP[i] = x; LOG[x] = i
    x <<= 1
    if x & Q: x ^= POLY
for i in range(Q - 1, 2 * Q): EXP[i] = EXP[i - (Q - 1)]
def mul(a, b): return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]
def inv(a): return EXP[(Q - 1) - LOG[a]]
def rank(M):
    M = [r[:] for r in M]; rk = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = inv(M[rk][c]); M[rk] = [mul(v, iv) for v in M[rk]]
        pr = M[rk]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]; lf = LOG[f]
                M[i] = [a ^ (EXP[lf + LOG[b]] if b else 0) for a, b in zip(M[i], pr)]
        rk += 1
        if rk == len(M): break
    return rk
def matmul(A, B, d):
    out = [[0] * d for _ in range(d)]
    for i in range(d):
        for j in range(d):
            s = 0
            for l in range(d): s ^= mul(A[i][l], B[l][j])
            out[i][j] = s
    return out
def ident(d): return [[1 if i == j else 0 for j in range(d)] for i in range(d)]
def rec(kk, d, rng):
    if kk == 1: return [[ident(d)]]
    out = []
    for child in range(2):
        T = [[rng.randrange(1, Q) for _ in range(d)] for _ in range(d)]
        for r in rec(kk // 2, d, rng): out.append(r + [matmul(T, e, d) for e in r])
    return out
def system(pattern, k, d, rng):
    leaves = pattern.split(); n = len(leaves)
    members = sorted(set("".join(l for l in leaves if l != ".")))
    L = len(members) - 1; idx = {m: i for i, m in enumerate(members)}
    brow = []
    for blk in range(n // k): brow += rec(k, d, rng)
    rows = []
    for xx, l in enumerate(leaves):
        if l == "." or len(l) < 2: continue
        ms = [idx[c] for c in l]
        for a, b in zip(ms, ms[1:]):
            for u in range(d):
                row = [0] * (L * k * d)
                for mem in (a, b):
                    if mem == 0: continue
                    base = (mem - 1) * k * d
                    for e in range(k):
                        for v in range(d): row[base + e * d + v] ^= brow[xx][e][u][v]
                rows.append(row)
    return rows
def best(pat, k, d, seeds=2):
    return max(rank(system(pat, k, d, random.Random(1000 * d + 7 * s + hash(pat) % 1000))) for s in range(seeds))
if __name__ == "__main__":
    src = sys.argv[1]; ds = [int(v) for v in sys.argv[2:]] or [1, 2]
    res = {}
    for line in open(src):
        pat = line.split("|")[0].strip()
        if not pat: continue
        leaves = pat.split(); n = len(leaves); k = n // 2
        w = sum(len(l) - 1 for l in leaves if l != "." and len(l) >= 2)
        key = tuple(w - best(pat, k, d) / d for d in ds)
        res[key] = res.get(key, 0) + 1
    print(src.split("/")[-1], "defect (weight - rank/d) for d =", ds, ":", res)
