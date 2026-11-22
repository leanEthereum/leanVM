#!/usr/bin/env python3
# Referee 52. Toy-size tests of Theorem 1.3 of note 50 against the known obstructions.
# Uses 52_even.c (null space of the contact conditions on a support, from the definition) and 52_list.c
# (exhaustive list oracle). Everything else (fields, subspace polynomials, flats, Gold members, the rate 1/16
# family, divisibility by a first integral, the splitting R = R_(0) + X R_(1) and gcd on random lines) is here.
#
# usage: python3 52_toy.py BINDIR [test ...]     tests: rank flat gold slack r16 f4 pencil half half22 (half22 is not in the default set: about 2 minutes)
import sys, os, subprocess, random, itertools

BIN = sys.argv[1] if len(sys.argv) > 1 else "."
MODS = {8: 0x11D, 10: 0x409, 12: 0x1053, 14: 0x4443, 16: 0x1100B}


class GF:
    def __init__(self, kf):
        self.kf = kf
        self.mod = MODS[kf]
        self.ord = (1 << kf) - 1
        self.exp = [0] * (2 * self.ord + 2)
        self.log = [0] * (self.ord + 1)
        v = 1
        seen = set()
        for i in range(self.ord):
            assert v not in seen, "modulus not primitive"
            seen.add(v)
            self.exp[i] = v
            self.log[v] = i
            v <<= 1
            if v >> kf:
                v ^= self.mod
        assert v == 1
        for i in range(self.ord, 2 * self.ord + 2):
            self.exp[i] = self.exp[i - self.ord]

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[self.ord - self.log[a]]

    def pw(self, a, e):
        if e == 0:
            return 1
        if a == 0:
            return 0
        return self.exp[(self.log[a] * e) % self.ord]

    # univariate polynomials: lists, low degree first
    def padd(self, a, b):
        n = max(len(a), len(b))
        r = [0] * n
        for i, x in enumerate(a):
            r[i] ^= x
        for i, x in enumerate(b):
            r[i] ^= x
        return self.trim(r)

    @staticmethod
    def trim(a):
        while a and a[-1] == 0:
            a.pop()
        return a

    def pmul(self, a, b):
        if not a or not b:
            return []
        r = [0] * (len(a) + len(b) - 1)
        ex, lg = self.exp, self.log
        for i, x in enumerate(a):
            if x:
                lx = lg[x]
                for j, y in enumerate(b):
                    if y:
                        r[i + j] ^= ex[lx + lg[y]]
        return self.trim(r)

    def pdivmod(self, a, b):
        a = a[:]
        q = [0] * max(0, len(a) - len(b) + 1)
        ib = self.inv(b[-1])
        while len(a) >= len(b) and a:
            c = self.mul(a[-1], ib)
            s = len(a) - len(b)
            q[s] = c
            for i, y in enumerate(b):
                a[s + i] ^= self.mul(c, y)
            self.trim(a)
        return self.trim(q), a

    def pgcd(self, a, b):
        a, b = a[:], b[:]
        while b:
            a, b = b, self.pdivmod(a, b)[1]
        return a

    def peval(self, a, x):
        r = 0
        for c in reversed(a):
            r = self.mul(r, x) ^ c
        return r

    def subspace(self, basis):
        els = [0]
        for b in basis:
            els += [e ^ b for e in els]
        assert len(set(els)) == len(els), "dependent basis"
        return els

    def locator(self, pts):
        r = [1]
        for p in pts:
            r = self.pmul(r, [p, 1])
        return r


def run_even(F, pts, word, Delta, m, Z, cs, tests=None, dP=0):
    lines = ["%d %d" % (F.kf, F.mod), "%d %d %d %d" % (len(pts), Delta, m, Z), "%d %s" % (len(cs), " ".join(map(str, cs)))]
    lines += ["%d %d" % (a, y) for a, y in zip(pts, word)]
    tests = tests or []
    lines.append("%d %d" % (len(tests), dP))
    for P in tests:
        lines.append(" ".join(str(P[i]) if i < len(P) else "0" for i in range(dP + 1)))
    out = subprocess.run([os.path.join(BIN, "52_even")], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout.split("\n")
    h = out[0].split()
    info = {"U": int(h[1]), "rank": int(h[3]), "null": int(h[5]), "local": [int(x) for x in h[7:10]]}
    k = out[1].split()
    info["killed"], info["ntest"], info["control"] = int(k[1]), int(k[2]), int(k[3])
    mons = [(x, a, c) for c in cs for a in range(0, Z) if Delta * (a + c) < Z for x in range(0, Z - Delta * (a + c))]
    assert len(mons) == info["U"]
    basis = []
    for line in out[2:2 + info["null"]]:
        v = [int(t, 16) for t in line.split()]
        basis.append({mons[i]: v[i] for i in range(len(v)) if v[i]})
    return info, basis


def run_list(F, pts, word, Delta, A):
    lines = ["%d %d" % (F.kf, F.mod), "%d %d %d" % (len(pts), Delta, A)] + ["%d %d" % (a, y) for a, y in zip(pts, word)]
    out = subprocess.run([os.path.join(BIN, "52_list")], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout.strip().split("\n")
    res = []
    for line in out:
        if line.strip():
            t = [int(x) for x in line.split()]
            res.append((t[0], F.trim(t[1:])))
    return res


def agreement(F, P, pts, word):
    return sum(1 for a, y in zip(pts, word) if F.peval(P, a) == y)


# bivariate polynomials in (X, Y): dict {(x, a): coeff}
def bmul(F, A, B):
    r = {}
    ex, lg = F.exp, F.log
    for (x1, a1), c1 in A.items():
        l1 = lg[c1]
        for (x2, a2), c2 in B.items():
            k = (x1 + x2, a1 + a2)
            r[k] = r.get(k, 0) ^ ex[l1 + lg[c2]]
    return {k: v for k, v in r.items() if v}


def bfrob(F, A, q):
    return {(x * q, a * q): F.pw(c, q) for (x, a), c in A.items()}


def dX(E):
    return {(x - 1, a): c for (x, a), c in E.items() if x & 1}


def dY(E):
    return {(x, a - 1): c for (x, a), c in E.items() if a & 1}


def is_section(F, E, P):
    # E(X, P(X)) in F[X^2] ?
    by_a = {}
    for (x, a), c in E.items():
        by_a.setdefault(a, {})[x] = c
    amax = max(by_a)
    acc = []
    for a in range(amax, -1, -1):
        acc = F.pmul(acc, P)
        if a in by_a:
            co = [0] * (max(by_a[a]) + 1)
            for x, c in by_a[a].items():
                co[x] = c
            acc = F.padd(acc, co)
    return all(c == 0 for c in acc[1::2])


def divisible_by_power(F, R, cpart, apart, q):
    # R = R_0 + R_q Y1^q divisible by (c + a Y1)^q  iff  R_0 a^q = R_q c^q
    R0 = {(x, a): v for (x, a, c), v in R.items() if c == 0}
    Rq = {(x, a): v for (x, a, c), v in R.items() if c == q}
    lhs = bmul(F, R0, bfrob(F, apart, q))
    rhs = bmul(F, Rq, bfrob(F, cpart, q))
    return lhs == rhs


def split_parts(F, R, tau0):
    # R(X, u + X v, v) = R_(0)(X^2, u, v) + X R_(1)(X^2, u, v); returns the two parts at tau = tau0 as {(iu, iv): c}
    parts = [{}, {}]
    for (x, a, c), co in R.items():
        for j in range(a + 1):
            if j & ~a:
                continue
            par = (x + j) & 1
            val = F.mul(co, F.pw(tau0, (x + j - par) // 2))
            if val:
                k = (a - j, c + j)
                parts[par][k] = parts[par].get(k, 0) ^ val
    return [{k: v for k, v in p.items() if v} for p in parts]


def restrict_line(F, B, u0, v0, su, sv):
    # (u, v) = (u0 + su t, v0 + sv t)
    deg = max((iu + iv for (iu, iv) in B), default=0)
    out = [0] * (deg + 1)
    pu = [[1]]
    pv = [[1]]
    for _ in range(deg):
        pu.append(F.pmul(pu[-1], [u0, su]))
        pv.append(F.pmul(pv[-1], [v0, sv]))
    for (iu, iv), c in B.items():
        pr = F.pmul(pu[iu], pv[iv])
        for i, y in enumerate(pr):
            out[i] ^= F.mul(c, y)
    return F.trim(out)


def common_degree(F, R, rng, trials=3):
    # degree of gcd(R_(0), R_(1)) seen on random lines at random tau (minimum over trials)
    best = None
    for _ in range(trials):
        tau0 = rng.randrange(1, F.ord + 1)
        p0, p1 = split_parts(F, R, tau0)
        u0, v0, su, sv = [rng.randrange(1, F.ord + 1) for _ in range(4)]
        f0 = restrict_line(F, p0, u0, v0, su, sv)
        f1 = restrict_line(F, p1, u0, v0, su, sv)
        if not f0 and not f1:
            return None
        g = F.pgcd(f0, f1) if f0 and f1 else (f0 or f1)
        dg = len(g) - 1
        best = dg if best is None else min(best, dg)
    return best


def mult_graph(F, R, P):
    # largest mu with (Y0 - P(X))^mu dividing R: substitute Y0 = P + S, lowest power of S
    cs = sorted(set(c for (_, _, c) in R))
    amax = max(a for (_, a, _) in R)
    pw = [[1]]
    for _ in range(amax):
        pw.append(F.pmul(pw[-1], P))
    for k in range(amax + 1):
        for c in cs:
            acc = []
            for (x, a, cc), v in R.items():
                if cc != c or a < k or (k & ~a):
                    continue
                term = [0] * x + [F.mul(v, t) for t in pw[a - k]]
                acc = F.padd(acc, term)
            if acc:
                return k
    return amax + 1



def rand_comb(F, basis, rng):
    R = {}
    for b in basis:
        f = rng.randrange(1, F.ord + 1)
        for k, v in b.items():
            R[k] = R.get(k, 0) ^ F.mul(f, v)
    return {k: v for k, v in R.items() if v}


def subfield(F, N):
    assert F.kf % N == 0
    step = F.ord // ((1 << N) - 1)
    return [0] + [F.exp[i * step] for i in range((1 << N) - 1)]


def sub_basis(F, pts):
    basis = []
    span = {0}
    for p in pts:
        if p not in span:
            basis.append(p)
            span |= {s ^ p for s in span}
    return basis


def hyperplanes(F, basis):
    # all hyperplanes of span(basis): kernels of nonzero linear functionals (given by a 0/1 vector on the basis)
    N = len(basis)
    out = []
    for phi in range(1, 1 << N):
        els = []
        for mask in range(1 << N):
            if bin(mask & phi).count("1") % 2 == 0:
                e = 0
                for i in range(N):
                    if mask >> i & 1:
                        e ^= basis[i]
                els.append(e)
        out.append(els)
    return out


def flat_cubic(F, pts):
    n = len(pts)
    LD = F.locator(pts)  # X^n + ... + e0 X
    e0 = LD[1]
    Lm = LD[:n]  # L_D - X^n
    E = {(1, 3): 1}
    for i in range(1, n):
        if Lm[i]:
            E[(i - 1, 1)] = Lm[i]  # ((L_D - X^n)/X) Y
    E[(n // 2 - 1, 0)] = e0
    return E, e0


def slack_cubic(F, pts):
    n = len(pts)
    LD = F.locator(pts)
    e0 = LD[1]
    E = {(0, 3): 1}
    for i in range(1, n):
        if LD[i]:
            E[(i, 1)] = LD[i]
    E[(n // 2 + 1, 0)] = e0
    return E, e0


def report(tag, info, extra=""):
    print("  %s: unknowns %d, rank %d, nullity %d, local ranks %s %s" % (tag, info["U"], info["rank"], info["null"], info["local"], extra))


def structure_test(F, pts, word, Delta, A, q, m, E, members, Wdeg, delta, tag, rng):
    Z = m * A
    d = (Z - 1) // Delta
    info, basis = run_even(F, pts, word, Delta, m, Z, [0, q], members, Delta)
    # Theorem 1.3 part 1: if the component dE carries more than delta*d list members, every even explainer is
    # lambda*(dE)^q; and then part 3 gives |List| <= d^2 + |L_dE|, so if the known list is larger no explainer exists.
    on = sum(1 for P in members if is_section(F, E, P))
    forced = on > delta * d
    forced_none = forced and len(members) > d * d + on
    line = "(q, m, A) = (%d, %d, %d), d = %d, delta*d = %d, members known %d of which %d on dE (divisibility forced: %s; non-existence forced: %s)" % (
        q, m, A, d, delta * d, len(members), on, forced, forced_none)
    if info["null"] == 0:
        report(tag, info, "| " + line + " | no even explainer")
        return
    c, a = dX(E), dY(E)
    ndiv = sum(1 for b in basis if divisible_by_power(F, b, c, a, q))
    lam_count = sum(1 for j in range(0, Z) for i in range(0, Z) if i + Delta * j <= Z - 1 - q * Wdeg)
    report(tag, info, "| " + line + " | Lemma 0: random R kills %d of %d members (control polynomial killed: %d) | basis vectors divisible by (dE)^q: %d of %d | monomials available to lambda: %d" % (
        info["killed"], info["ntest"], info["control"], ndiv, info["null"], lam_count))
    if ndiv != info["null"]:
        R = rand_comb(F, basis, rng)
        print("     random R not of the form lambda*(dE)^q; degree of gcd(R_(0), R_(1)) on random lines: %s" % common_degree(F, R, rng))


def test_rank(rng):
    print("== rank: local rank at three arbitrary points of GF(2^8) x GF(2^8), support {1, Y1^q} with total degree < m + q")
    F = GF(8)
    for q, ms in ((2, (3, 4, 5, 8, 13, 20)), (4, (7, 8, 9, 14, 20)), (8, (15, 16, 17, 20)), (16, (31,))):
        res = []
        for m in ms:
            pts = rng.sample(range(256), 2 if q == 16 else 3)
            word = [rng.randrange(256) for _ in pts]
            info, _ = run_even(F, pts, word, 1, m, m + q, [0, q])
            rho = m * m - (q - 1) * m + q * (3 * q - 1) // 2
            res.append((m, info["local"][: len(pts)], rho))
        print("  q=%d: (m, local ranks, formula) %s" % (q, res))
    # full support Y1-degree <= B against R(m, B)
    res = []
    for m, B in ((5, 2), (8, 2), (11, 2), (14, 2), (9, 3), (12, 4), (18, 5)):
        pts = rng.sample(range(256), 3)
        word = [rng.randrange(256) for _ in pts]
        info, _ = run_even(F, pts, word, 1, m, m + B, list(range(B + 1)))
        Rf = sum((s + 1) * (B + 1) - max(2 * s - m + 1, 0) * max(s + B - m + 1, 0) for s in range(m))
        res.append((m, B, info["local"], Rf))
    print("  full support: (m, B, local ranks, R(m, B)) %s" % res)


def flats_of(F, pts):
    n = len(pts)
    basis = sub_basis(F, pts)
    out = []
    for V in hyperplanes(F, basis):
        LV = F.locator(V)
        P = LV[1:n // 2]  # (L_V - X^(n/2)) / X
        out.append(F.trim(P[:]))
    return out


def test_flat(rng):
    print("== flat: rate 1/4, word x^(n/2-1) on a subspace, degree < n/4; all n-1 flats lie on the flat cubic (b = 1)")
    # n = 16 and 32: exhaustive list
    F = GF(8)
    for N, A in ((4, 7), (5, 15), (5, 13)):
        n = 1 << N
        pts = F.subspace([F.exp[i] for i in range(N)])
        word = [F.pw(a, n // 2 - 1) for a in pts]
        Delta = n // 4 - 1
        E, e0 = flat_cubic(F, pts)
        lst = run_list(F, pts, word, Delta, A)
        onE = sum(1 for ag, P in lst if is_section(F, E, P))
        print("  n=%d (span(1..x^%d) in GF(2^8)), Delta=%d: exhaustive list at agreement >= %d: %d members, %d of them sections of the flat cubic" % (n, N - 1, Delta, A, len(lst), onE))
        members = [P for ag, P in lst]
        for q, m in ((2, 4), (2, 5), (2, 6), (4, 8)):
            structure_test(F, pts, word, Delta, A, q, m, E, members, 3 * Delta + 1, 3, "n=%d" % n, rng)
    # validation of the oracle against the counts of notes 35 and 41 on this domain (31 at 15, 20 at 11 of which 18 sections, 627 at 10)
    pts = F.subspace([F.exp[i] for i in range(5)])
    word = [F.pw(a, 15) for a in pts]
    E, e0 = flat_cubic(F, pts)
    lst = run_list(F, pts, word, 7, 10)
    hist, sec = {}, {}
    for ag, P in lst:
        hist[ag] = hist.get(ag, 0) + 1
        if is_section(F, E, P):
            sec[ag] = sec.get(ag, 0) + 1
    print("  oracle validation, n=32 (span(1..x^4) in GF(2^8)): list by agreement %s, sections of the cubic by agreement %s" % (sorted(hist.items()), sorted(sec.items())))
    # n = 64 on a random subspace of GF(2^8): the 63 flats
    basis = []
    while len(basis) < 6:
        c = rng.randrange(1, 256)
        try:
            F.subspace(basis + [c])
            basis.append(c)
        except AssertionError:
            pass
    pts = F.subspace(basis)
    n = 64
    Delta = 15
    word = [F.pw(a, 31) for a in pts]
    E, e0 = flat_cubic(F, pts)
    fl = flats_of(F, pts)
    assert len(fl) == 63 and all(agreement(F, P, pts, word) >= 31 and len(P) <= Delta + 1 for P in fl)
    print("  n=64 (random subspace of GF(2^8)): 63 flats verified (degree <= 15, agreement >= 31), all sections of the cubic: %s" % all(is_section(F, E, P) for P in fl))
    for q, m, A in ((2, 4, 25), (2, 4, 31), (2, 5, 25), (2, 6, 27)):
        structure_test(F, pts, word, Delta, A, q, m, E, fl, 3 * Delta + 1, 3, "n=64", rng)


def gold_members_F64(F, pts, word):
    # members of the flat word on D = F_64 at agreement 27, from z^2 + z = (X^64 + X) g(X^2)^2 with g = g0 + g2 X^4
    # (derived in the report, Section 3; every candidate is verified by its agreement afterwards)
    F64 = pts
    F8 = [x for x in F64 if F.pw(x, 8) == x]
    found = {}
    for g0 in F64:
        for g2 in F8:
            if g2 == 0:
                continue
            for z0 in (0, 1):
                z = [0] * 37
                z[0] = z0
                t = F.mul(g0, g0)
                i = 1
                while i <= 32:
                    z[i] ^= t
                    t = F.mul(t, t)
                    i *= 2
                t = F.mul(g2, g2)
                i = 9
                while i <= 36:
                    z[i] ^= t
                    t = F.mul(t, t)
                    i *= 2
                g = [g0, 0, 0, 0, g2]
                qq, rr = F.pdivmod(F.trim(z[:]), g)
                if rr:
                    continue
                s = qq + [0] * (33 - len(qq))
                s[32] ^= 1
                if s[0]:
                    continue
                P = F.trim(s[1:])
                if len(P) <= 16 and agreement(F, P, pts, word) >= 27:
                    found[tuple(P)] = 1
    return [list(p) for p in found]


def gold_members_F128(F, pts, word):
    # the same construction on D = F_128 at agreement 55: g = g0 + g4^8 X^4 + g4 X^8 (g0, g4 in F_128, g4 != 0),
    # z_(4k+1) = g_k^2, z_(2i) = z_i^2, deg z <= 72; every candidate is verified by its agreement afterwards
    found = {}
    for g4 in pts:
        if g4 == 0:
            continue
        g2 = F.pw(g4, 8)
        for g0 in pts:
            base = [0] * 73
            for start, gk in ((1, g0), (9, g2), (17, g4)):
                t = F.mul(gk, gk)
                i = start
                while i <= 72:
                    base[i] ^= t
                    t = F.mul(t, t)
                    i *= 2
            g = [g0, 0, 0, 0, g2, 0, 0, 0, g4]
            for z0 in (0, 1):
                z = base[:]
                z[0] = z0
                qq, rr = F.pdivmod(F.trim(z), g)
                if rr:
                    continue
                s = qq + [0] * (65 - len(qq))
                s[64] ^= 1
                if s[0]:
                    continue
                P = F.trim(s[1:])
                if len(P) <= 32 and agreement(F, P, pts, word) >= 55:
                    found[tuple(P)] = 1
    return [list(p) for p in found]


def test_gold(rng):
    print("== gold: rate 1/4, word x^(n/2-1) on D = F_(2^N) (note 43, Section 4.2)")
    # N = 5: exhaustive
    F = GF(10)
    pts = subfield(F, 5)
    n = 32
    Delta = 7
    word = [F.pw(a, 15) for a in pts]
    E, e0 = flat_cubic(F, pts)
    lst = run_list(F, pts, word, Delta, 11)
    hist = {}
    for ag, P in lst:
        hist[ag] = hist.get(ag, 0) + 1
    onE = sum(1 for ag, P in lst if is_section(F, E, P))
    off = [(ag, P) for ag, P in lst if not is_section(F, E, P)]
    off0 = sum(1 for ag, P in off if F.peval(P, 0) == 0)
    print("  N=5: exhaustive list at agreement >= 11: %d members, by agreement %s; sections of the flat cubic: %d; not sections: %d, of which %d agree with the word at 0 (so have 10 agreements off 0)" % (
        len(lst), sorted(hist.items()), onE, len(off), off0))
    members = [P for ag, P in lst]
    for q, m in ((2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (4, 8)):
        structure_test(F, pts, word, Delta, 11, q, m, E, members, 3 * Delta + 1, 3, "N=5 A=11", rng)
    for q, m in ((2, 4), (2, 6)):
        structure_test(F, pts, word, Delta, 13, q, m, E, [P for ag, P in lst if ag >= 13], 3 * Delta + 1, 3, "N=5 A=13", rng)
    # N = 6
    F = GF(12)
    pts = subfield(F, 6)
    n = 64
    Delta = 15
    word = [F.pw(a, 31) for a in pts]
    E, e0 = flat_cubic(F, pts)
    fl = flats_of(F, pts)
    gm = gold_members_F64(F, pts, word)
    ags = sorted(set(agreement(F, P, pts, word) for P in gm))
    members = fl + gm
    assert len(set(tuple(P) for P in members)) == len(members)
    print("  N=6: 63 flats (agreement 31) and %d further members constructed and verified (degree <= 15, agreements %s); sections of the flat cubic: %d of %d" % (
        len(gm), ags, sum(1 for P in members if is_section(F, E, P)), len(members)))
    for q, m, A in ((2, 4, 25), (4, 8, 25), (2, 6, 27), (4, 8, 27)):
        structure_test(F, pts, word, Delta, A, q, m, E, members, 3 * Delta + 1, 3, "N=6", rng)
    # N = 7
    F = GF(14)
    pts = subfield(F, 7)
    n = 128
    Delta = 31
    word = [F.pw(a, 63) for a in pts]
    E, e0 = flat_cubic(F, pts)
    fl = flats_of(F, pts)
    gm = gold_members_F128(F, pts, word)
    members = fl + gm
    assert len(set(tuple(P) for P in members)) == len(members)
    print("  N=7: 127 flats (agreement 63) and %d further members constructed and verified (degree <= 31, agreements %s); sections of the flat cubic: %d of %d" % (
        len(gm), sorted(set(agreement(F, P, pts, word) for P in gm)), sum(1 for P in members if is_section(F, E, P)), len(members)))
    for q, m, A in ((2, 4, 55), (2, 6, 55)):
        structure_test(F, pts, word, Delta, A, q, m, E, members, 3 * Delta + 1, 3, "N=7", rng)


def test_slack(rng):
    print("== slack: rate 1/4 with the analysis degree, word x^(n/2), degree <= n/4, agreement n/2 = sqrt(n Delta) (note 41, Section 4.4)")
    F = GF(8)
    for N in (5, 6):
        n = 1 << N
        basis = [F.exp[i] for i in range(N)] if N == 5 else None
        if basis is None:
            basis = []
            while len(basis) < N:
                c = rng.randrange(1, 256)
                try:
                    F.subspace(basis + [c])
                    basis.append(c)
                except AssertionError:
                    pass
        pts = F.subspace(basis)
        Delta = n // 4
        word = [F.pw(a, n // 2) for a in pts]
        E, e0 = slack_cubic(F, pts)
        members = []
        for V in hyperplanes(F, basis):
            LV = F.locator(V)
            lam = next(p for p in pts if p not in set(V))
            for shift in (0, F.peval(LV, lam)):
                P = LV[:n // 2]  # X^(n/2) - Z_H = L_V - X^(n/2) + const
                P = P[:]
                P[0] ^= shift
                members.append(F.trim(P))
        ok = all(agreement(F, P, pts, word) >= n // 2 and len(P) <= Delta + 1 for P in members)
        if N == 5:
            lst = run_list(F, pts, word, Delta, n // 2)
            print("  n=32: exhaustive list at agreement >= 16: %d members; the 62 affine flats are among them: %s" % (len(lst), set(tuple(P) for P in members) <= set(tuple(P) for a, P in lst)))
        print("  n=%d: %d affine flats verified: %s; sections of the cubic E': %d" % (n, len(members), ok, sum(1 for P in members if is_section(F, E, P))))
        for q, m, A in ((2, 4, n // 2), (2, 5, n // 2), (2, 6, n // 2)) + (((4, 8, n // 2),) if N == 5 else ()):
            structure_test(F, pts, word, Delta, A, q, m, E, members, 3 * Delta, 3, "n=%d" % n, rng)


def test_r16(rng):
    print("== r16: rate 1/16, D = F_256, word x^(n/4) = x^64, degree < 16, agreement 52 (note 43, Proposition 6.4)")
    F = GF(8)
    pts = [0] + [F.exp[i] for i in range(255)]
    n = 256
    Delta = 15
    word = [F.pw(a, 64) for a in pts]
    E = {(0, 5): 1, (1, 1): 1, (65, 0): 1}
    F4 = [x for x in pts if F.pw(x, 4) == x]
    F16 = [x for x in pts if F.pw(x, 16) == x]
    found = {}
    for mu0 in pts:
        for mu1 in pts:
            if mu1 == 0 or F.pw(mu1, 4) not in F16:
                continue
            z = [0] * 69
            t = F.pw(mu0, 4)
            for e in (1, 4, 16, 64):
                z[e] ^= t
                t = F.pw(t, 4)
            t = F.pw(mu1, 4)
            z[17] ^= t
            z[68] ^= F.pw(t, 4)
            mu = [mu0, 0, 0, 0, mu1]
            for eta in F4:
                zz = z[:]
                zz[0] ^= eta
                qq, rr = F.pdivmod(F.trim(zz), mu)
                if rr:
                    continue
                P = qq + [0] * (65 - len(qq))
                P[64] ^= 1
                P = F.trim(P)
                if len(P) <= 16 and agreement(F, P, pts, word) >= 52:
                    found[tuple(P)] = 1
    members = [list(p) for p in found]
    print("  %d distinct polynomials of degree <= 15 with agreement >= 52 constructed and verified; sections of dE, E = Y^5 + XY + X^65: %d" % (
        len(members), sum(1 for P in members if is_section(F, E, P))))
    structure_test(F, pts, word, Delta, 52, 2, 4, E, members, 5 * Delta, 5, "n=256", rng)


def test_f4(rng):
    print("== f4: rate 1/16, D = F_n as an F_4-space, word x^(n/4-1), degree < n/16: the (n-1)/3 F_4-hyperplanes lie on the quintic E_4 = X^3 Y^5 + Y + X^(n/4-1) (note 43, Proposition 6.3)")
    for kf, N, As in ((12, 6, (15, 11)), (8, 8, (63, 41))):
        F = GF(kf)
        pts = subfield(F, N)
        n = 1 << N
        Delta = n // 16 - 1
        word = [F.pw(a, n // 4 - 1) for a in pts]
        E = {(3, 5): 1, (0, 1): 1, (n // 4 - 1, 0): 1}
        seen = {}
        for beta in pts[1:]:
            V = []
            for x in pts:
                z = F.mul(beta, x)
                tr = 0
                for _ in range(N // 2):
                    tr ^= z
                    z = F.pw(z, 4)
                if tr == 0:
                    V.append(x)
            key = tuple(sorted(V))
            if key in seen:
                continue
            LV = F.locator(V)
            P = F.trim(LV[1:n // 4])
            assert len(P) <= Delta + 1 and agreement(F, P, pts, word) >= n // 4 - 1
            seen[key] = P
        members = list(seen.values())
        print("  n=%d: %d F_4-hyperplanes verified (degree <= %d, agreement >= %d); sections of dE_4: %d" % (n, len(members), Delta, n // 4 - 1, sum(1 for P in members if is_section(F, E, P))))
        if N == 6:
            for A in As:
                lst = run_list(F, pts, word, Delta, A)
                hist = {}
                for ag, P in lst:
                    hist[ag] = hist.get(ag, 0) + 1
                print("  n=64: exhaustive list at agreement >= %d: %s; sections of dE_4: %d of %d" % (A, sorted(hist.items()), sum(1 for ag, P in lst if is_section(F, E, P)), len(lst)))
        for A in As:
            structure_test(F, pts, word, Delta, A, 2, 4, E, members, 5 * Delta + 3, 5, "n=%d" % n, rng)


def test_pencil(rng):
    print("== pencil: rate 1/8, word x^(n/4-1) on a subspace, degree < n/8: the codimension 2 subspaces lie on the pencil dE_theta of note 43 (Q8), not on one component")
    F = GF(8)
    basis = []
    while len(basis) < 6:
        c = rng.randrange(1, 256)
        try:
            F.subspace(basis + [c])
            basis.append(c)
        except AssertionError:
            pass
    pts = F.subspace(basis)
    n = 64
    Delta = 7
    A = 15
    word = [F.pw(a, 15) for a in pts]
    members = {}
    thetas = {}
    for H1 in hyperplanes(F, basis):
        b1 = sub_basis(F, H1)
        for V in hyperplanes(F, b1):
            key = tuple(sorted(V))
            if key in members:
                continue
            LV = F.locator(V)  # degree 16
            P = F.trim(LV[1:16])
            assert len(P) <= 8 and agreement(F, P, pts, word) >= 15
            members[key] = P
            img = sorted(set(F.peval(LV, p) for p in pts))  # L_V(D) = {0, a, b, a + b}; L_D = L_V^4 + theta_2 L_V^2 + theta_1 L_V
            assert len(img) == 4
            a_, b_ = img[1], img[2]
            th2 = F.mul(a_, a_) ^ F.mul(a_, b_) ^ F.mul(b_, b_)
            thetas[th2] = thetas.get(th2, 0) + 1
    print("  n=64: %d members (codimension 2 subspaces) verified; number of distinct theta_2 (the member of the pencil that carries the flat): %d, largest class %d" % (len(members), len(thetas), max(thetas.values())))
    mem = list(members.values())
    for q, m in ((2, 4), (2, 5), (2, 6), (2, 8), (4, 8)):
        Z = m * A
        d = (Z - 1) // Delta
        info, basis_ = run_even(F, pts, word, Delta, m, Z, [0, q], mem, Delta)
        report("(q, m) = (%d, %d), d = %d, d^2 = %d" % (q, m, d, d * d), info, "| consistent with Theorem 1.3: %s" % (info["null"] == 0 or "CHECK"))


def test_half(rng, big=False):
    print("== half: rate 1/2 above the Johnson radius (the only place where toy certificates exist); list by exhaustive enumeration")
    F = GF(8)
    cases = ((16, 7, 12, ((2, 4), (2, 6), (4, 8))), (16, 7, 11, ((2, 6), (2, 9))), (32, 15, 23, ((2, 6),)))
    if big:
        cases = ((32, 15, 22, ((2, 12),)),)
    for n, Delta, A, qm in cases:
        for wname in ("random", "planted", "two"):
            pts = rng.sample(range(256), n)
            if wname == "random":
                word = [rng.randrange(256) for _ in pts]
            elif wname == "planted":
                P = [rng.randrange(256) for _ in range(Delta + 1)]
                word = [F.peval(P, a) for a in pts]
                for i in rng.sample(range(n), n - A):
                    word[i] ^= rng.randrange(1, 256)
            else:
                # two codewords at distance n - Delta, the word follows one on A points and the other elsewhere
                P1 = [rng.randrange(256) for _ in range(Delta + 1)]
                loc = F.locator(pts[:Delta])
                P2 = F.padd(P1, loc)
                word = [F.peval(P1, a) for a in pts]
                for i in range(Delta, Delta + (n - A)):
                    word[i] = F.peval(P2, pts[i])
            lst = run_list(F, pts, word, Delta, A)
            members = [P for ag, P in lst]
            for q, m in qm:
                Z = m * A
                d = (Z - 1) // Delta
                cnt = sum((Z - Delta * a) for a in range(0, Z) if Z - Delta * a > 0) + sum((Z - Delta * (a + q)) for a in range(0, Z) if Z - Delta * (a + q) > 0)
                rho = m * m - (q - 1) * m + q * (3 * q - 1) // 2
                info, basis = run_even(F, pts, word, Delta, m, Z, [0, q], members, Delta)
                extra = "| count %d - n*rho %d = %d | list %d, d^2 = %d" % (cnt, n * rho, cnt - n * rho, len(members), d * d)
                if info["null"]:
                    R = rand_comb(F, basis, rng)
                    mus = [mult_graph(F, R, P) for P in members]
                    extra += " | Lemma 0: %d of %d killed, control %d | degree of gcd(R_(0), R_(1)) on random lines: %s; multiplicities of the factors Y0 - P, P in the list: %s (squares account for degree %d)" % (
                        info["killed"], info["ntest"], info["control"], common_degree(F, R, rng), mus, sum(2 * (mu // 2) for mu in mus))
                report("n=%d Delta=%d A=%d %s (q, m) = (%d, %d)" % (n, Delta, A, wname, q, m), info, extra)


if __name__ == "__main__":
    tests = sys.argv[2:] or ["rank", "flat", "gold", "slack", "r16", "f4", "pencil", "half"]
    rng = random.Random(5252)
    for t in tests:
        if t == "half22":
            test_half(rng, big=True)
            continue
        {"rank": test_rank, "flat": test_flat, "gold": test_gold, "slack": test_slack, "r16": test_r16, "f4": test_f4, "pencil": test_pencil, "half": test_half}[t](rng)
