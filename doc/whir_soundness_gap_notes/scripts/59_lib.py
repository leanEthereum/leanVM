# 59_lib.py: GF(2^m) arithmetic (pure Python, log tables) and helpers for note 59.
# Positions of the domain are the integers v < 2^N; the field element of position v is v
# (polynomial basis), so D = span(1, x, ..., x^(N-1)) and the cube window of v is v and its N bit flips.
IRRED = {3: 0xB, 4: 0x13, 5: 0x25, 6: 0x43, 7: 0x83, 8: 0x11B, 9: 0x211, 10: 0x409,
         11: 0x805, 12: 0x1053, 13: 0x201B, 14: 0x4443, 16: 0x1002B, 17: 0x20009}


class GF:
    def __init__(self, m):
        self.m, self.q, self.poly = m, 1 << m, IRRED[m]
        q = self.q
        for g in range(2, q):
            exp, x, ok = [1] * (2 * q), 1, True
            for i in range(1, q - 1):
                x = self._slow(x, g)
                if x == 1:
                    ok = False
                    break
                exp[i] = x
            if ok:
                break
        for i in range(q - 1, 2 * q):
            exp[i] = exp[i - (q - 1)]
        self.exp, self.log = exp, [0] * q
        for i in range(q - 1):
            self.log[exp[i]] = i

    def _slow(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a >> self.m:
                a ^= self.poly
        return r

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[(self.q - 1 - self.log[a]) % (self.q - 1)]

    def pw(self, a, e):
        if e == 0:
            return 1
        if a == 0:
            return 0
        return self.exp[(self.log[a] * e) % (self.q - 1)]

    def rank(self, rows):
        """Rank of a matrix (list of lists) over the field."""
        M = [r[:] for r in rows]
        rk, ncol = 0, len(M[0]) if M else 0
        exp, log, q1 = self.exp, self.log, self.q - 1
        for c in range(ncol):
            p = next((i for i in range(rk, len(M)) if M[i][c]), None)
            if p is None:
                continue
            M[rk], M[p] = M[p], M[rk]
            lp = log[M[rk][c]]
            for i in range(rk + 1, len(M)):
                if M[i][c]:
                    f = (log[M[i][c]] - lp) % q1
                    Mi, Mr = M[i], M[rk]
                    for j in range(c, ncol):
                        if Mr[j]:
                            Mi[j] ^= exp[log[Mr[j]] + f]
            rk += 1
            if rk == len(M):
                break
        return rk


def span(gens):
    s = [0]
    for g in gens:
        s += [a ^ g for a in s]
    return s


def subspace_poly_values(F, U, pts):
    """Values of L_U(X) = prod_{u in U} (X + u) at the points."""
    out = []
    for x in pts:
        v = 1
        for u in U:
            v = F.mul(v, x ^ u)
        out.append(v)
    return out


def window(v, N):
    return [v] + [v ^ (1 << i) for i in range(N)]


def deficiency(F, vals, N):
    """vals[j][v] = value of the j-th basis polynomial of V at position v.
    Returns the list of Delta_x(V) = dim V - rank(V restricted to the window of x)."""
    L, n = len(vals), 1 << N
    out = []
    for v in range(n):
        W = window(v, N)
        out.append(L - F.rank([[vals[j][w] for w in W] for j in range(L)]))
    return out


def additive_values(F, U_gens, N):
    """Values on all positions of the subspace polynomial of span(U_gens), by F_2-linearity."""
    U = span(U_gens)
    basis = subspace_poly_values(F, U, [1 << l for l in range(N)])
    out = [0] * (1 << N)
    for v in range(1, 1 << N):
        low = v & -v
        out[v] = out[v ^ low] ^ basis[low.bit_length() - 1]
    return out, len(U)
