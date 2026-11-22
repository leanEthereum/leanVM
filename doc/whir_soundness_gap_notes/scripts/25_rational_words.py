"""Researcher 25. Rational words P/Q against the top word, with the exhaustive list oracle 02_lists (note 25, section 3).

A codeword c of degree <= d agrees with w = P/Q on S iff Z_S divides P - cQ. With T = |S|, m = T - d - 1 and
q = deg Q = m + 1 this says Z_S = g P modulo Q for a scalar g: the members are the T-sets whose locators have
proportional residues modulo Q. The top word is the case "Q at infinity".

For a fixed T-set S0 (a non-periodic member of the 5n/8 family of note 02) the script builds
  top:      w = Z_S0 restricted to D (the word of the family, modulo codewords),
  rational: w = (Z_S0 mod Q)/Q for several Q of degree m + 1,
and prints the exact number of polynomials of degree <= d by agreement >= T for each, all words, no assumption.
Proposition 3.1 (fewer than m + 1 poles give no member at all) is checked with random P and deg Q = m.

usage: python3 25_rational_words.py <02_lists binary> N [seed]      (N = 4: under a second; N = 5: seven oracle calls of about two minutes each, three at a time)
"""
import sys, os, subprocess, random, importlib.util
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
F = gf.GF(64)
binary, N = sys.argv[1], int(sys.argv[2])
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
rng = random.Random(seed)
n = 1 << N
basis = gf.random_basis(F, N, rng)
D = gf.span(basis)
d = n // 2          # degree bound (slack one), k = d + 1 coefficients
T = 5 * n // 8
m = T - d - 1       # number of conditions is m, the pure pole count is q = m + 1
q = m + 1


def poly_mod(p, mod):
    p = p[:]
    dm = len(mod) - 1
    inv = F.inv(mod[-1])
    for i in range(len(p) - 1, dm - 1, -1):
        c = F.mul(p[i], inv)
        if c:
            for j in range(dm + 1):
                p[i - dm + j] ^= F.mul(c, mod[j])
    return p[:dm]


def lin_poly(c):  # linearized coefficients -> full coefficient list
    out = [0] * ((1 << (len(c) - 1)) + 1)
    for i, ci in enumerate(c):
        out[1 << i] = ci
    return out


def oracle(words, tmin):
    inp = " ".join(f"{x:x}" for x in D) + "\n" + "\n".join(" ".join(f"{v:x}" for v in w) for w in words) + "\n"
    return subprocess.run([binary, "profile", "64", "1b", str(n), str(d + 1), str(tmin)], input=inp, capture_output=True, text=True).stdout.splitlines()


# U of size n/8, the top word L_U^5, and one member S0 that is not a union of cosets of U
Ub = basis[: N - 3]
LU = lin_poly(gf.subspace_poly(F, Ub))
top = [1]
for _ in range(5):
    top = F.poly_mul(top, LU)
top_vals = [F.poly_eval(top, x) for x in D]
inp = " ".join(f"{x:x}" for x in D) + "\n" + " ".join(f"{v:x}" for v in top_vals) + "\n"
mem = subprocess.run([binary, "members", "64", "1b", str(n), str(d + 1), str(T)], input=inp, capture_output=True, text=True).stdout.split()
masks = []
for tok in mem:
    try:
        v = int(tok, 16)
    except ValueError:
        continue
    if bin(v).count("1") == T:
        masks.append(v)
usize = 1 << (N - 3)
def periodic(mask):
    return all((mask >> i & 1) == (mask >> (i ^ u) & 1) for i in range(n) for u in range(1, usize))
nonper = [mk for mk in masks if not periodic(mk)]
print(f"N = {N}, n = {n}, degree <= {d}, T = {T}, m = {m}: the top word L_U^5 has {len(masks)} members at agreement {T}, {len(nonper)} of them not U-periodic")
S0 = [D[i] for i in range(n) if nonper[0] >> i & 1]
Z0 = F.locator(S0)


def outside():  # a random element of K outside D
    while True:
        b = F.rand(rng)
        if b not in D:
            return b


cases = []
cases.append(("top (Q at infinity), w = Z_S0", [F.poly_eval(Z0, x) for x in D]))
def add(name, Q):
    P = poly_mod(Z0, Q)
    vals = []
    for x in D:
        qx = F.poly_eval(Q, x)
        assert qx != 0
        vals.append(F.mul(F.poly_eval(P, x), F.inv(qx)))
    cases.append((name, vals))

add(f"{q} random simple poles", F.locator([outside() for _ in range(q)]))
b = outside()
add(f"one pole of order {q}", F.locator([b] * q))
b = outside()
if q == usize:
    add("poles = a coset b + U (Q = L_U + L_U(b))", F.locator([b ^ u for u in D[:usize]]))
other = gf.random_basis(F, N - 3, rng)
others = [x for x in D if x not in D[:usize]]
V2 = gf.span([others[3], others[11]][: N - 3]) if N - 3 <= 2 else gf.span(others[:1])
b = outside()
add(f"{q} poles in the coset b + D", F.locator([b ^ D[i] for i in rng.sample(range(n), q)]))
b = outside()
add(f"poles = b + V, V another subspace of D of size {len(V2)}" + ("" if len(V2) == q else " (one pole repeated)"),
    F.locator(([b ^ v for v in V2] * q)[:q]))
# fewer poles than m + 1: random numerator, deg Q = m (Proposition 3.1 says no member at agreement >= T)
if m >= 1:
    Q = F.locator([outside() for _ in range(m)])
    P = [F.rand(rng) for _ in range(m + d + 1)]
    cases.append((f"random P of degree {m + d}, {m} simple poles (Proposition 3.1: nothing at agreement >= d + m + 1 = {T})",
                  [F.mul(F.poly_eval(P, x), F.inv(F.poly_eval(Q, x))) for x in D]))

# one oracle call per word (each well under ten minutes at N = 5), three at a time
from concurrent.futures import ThreadPoolExecutor
with ThreadPoolExecutor(max_workers=3) as ex:
    outs = list(ex.map(lambda v: oracle([v], T), [v for _, v in cases]))
print(f"number of polynomials of degree <= {d} by exact agreement (>= {T}), exhaustive over all polynomials:")
for (name, _), out in zip(cases, outs):
    line = out[0] if out else ""
    print(f"  {name:75s} {line.strip() or '(none)'}", flush=True)
