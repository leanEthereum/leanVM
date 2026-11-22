#!/usr/bin/env python3
"""Note 78: packed codes (the '#<int>' names of 78_var.h) and structure flags of F_2 matrices built from the named ones.
usage: 78_mat.py v name [name ...]   names: id rev rot up dn sw<i>, products 'a*b' (first a then... (a*b) e = a (b e)), 'a^-1'
Flags: lowpres/highpres = number of levels i (1..v-1) with M V_i = V_i (low bits) / M U_i = U_i (high bits);
lu = all top principal minors nonsingular."""
import sys
def named(nm, v):
    A = [1 << l for l in range(v)]
    if nm == 'id': return A
    if nm == 'rev': return [1 << (v - 1 - l) for l in range(v)]
    if nm == 'rot': return [1 << ((l + v - 1) % v) for l in range(v)]
    if nm == 'up': return [A[l] | (1 << (l + 1)) if l + 1 < v else A[l] for l in range(v)]
    if nm == 'cr':
        A[0] = 1 << (v - 1); A[v - 1] = (1 << (v - 1)) | 1; return A
    if nm == 'ud': return mul(named('up', v), named('dn', v), v)
    if nm == 'du': return mul(named('dn', v), named('up', v), v)
    if nm == 'dn': return [A[l] | (1 << (l - 1)) if l >= 1 else A[l] for l in range(v)]
    if nm.startswith('sw'):
        i = int(nm[2:]); A[i], A[i + 1] = A[i + 1], A[i]; return A
    if nm.startswith('#'):
        c = int(nm[1:], 0); return [(c >> (l * v)) & ((1 << v) - 1) for l in range(v)]
    raise ValueError(nm)
def mul(A, B, v):
    out = []
    for l in range(v):
        row = 0
        for j in range(v):
            if (A[l] >> j) & 1: row ^= B[j]
        out.append(row)
    return out
def inv(A, v):
    a = list(A); b = [1 << l for l in range(v)]
    for c in range(v):
        p = next(l for l in range(c, v) if (a[l] >> c) & 1)
        a[p], a[c] = a[c], a[p]; b[p], b[c] = b[c], b[p]
        for l in range(v):
            if l != c and (a[l] >> c) & 1: a[l] ^= a[c]; b[l] ^= b[c]
    return b
def rank(rows, ncol):
    rows = list(rows); r = 0
    for c in range(ncol):
        p = next((i for i in range(r, len(rows)) if (rows[i] >> c) & 1), None)
        if p is None: continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and (rows[i] >> c) & 1: rows[i] ^= rows[r]
        r += 1
    return r
def parse(expr, v):
    M = None
    for f in expr.split('*'):
        A = inv(named(f[:-3], v), v) if f.endswith('^-1') else named(f, v)
        M = A if M is None else mul(M, A, v)
    return M
def flags(M, v):
    low = sum(all((M[l] & ((1 << i) - 1)) == 0 for l in range(i, v)) for i in range(1, v))
    high = sum(all((M[l] >> i) == 0 for l in range(i)) for i in range(1, v))
    lu = all(rank([M[l] >> (v - j) for l in range(v - j, v)], j) == j for j in range(1, v + 1))
    return low, high, lu
if __name__ == '__main__':
    v = int(sys.argv[1])
    for e in sys.argv[2:]:
        M = parse(e, v); low, high, lu = flags(M, v)
        print(f"{e}: #{sum(M[l] << (l * v) for l in range(v))} rows {' '.join(format(x, '0%db' % v) for x in M)} ones {sum(bin(x).count('1') for x in M)} lowpres {low} highpres {high} lu {int(lu)}")
