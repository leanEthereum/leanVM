"""Tangent-line lists for k = 2 (report 02, section 8): a non-common-top family.

A a Sidon set in D (all pairwise sums distinct). Word w(a + a') = a a' for a != a' in A (random elsewhere).
The line P_a(X) = a X + a^2 agrees with w on {a + a' : a' in A, a' != a}: |A| lines with |A| - 1 agreements each.
Checked with the exhaustive oracle on D = span(1, ..., x^(N-1)) in GF(2^64).

usage: python3 02_sidon_lines.py <lists-binary> N
"""
import sys, os, subprocess, random, importlib.util
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
F = gf.GF(64)
binary, N = sys.argv[1], int(sys.argv[2])
n = 1 << N
D = list(range(n))  # power basis: the element with coordinates i is the integer i
best = []
rng = random.Random(4)
for trial in range(3000):
    A, sums = [], set()
    order = D[:]
    rng.shuffle(order)
    for a in order:
        new = {a ^ b for b in A}
        if not (new & sums) and 0 not in new:
            A.append(a)
            sums |= new
    if len(A) > len(best):
        best = A
A = best
w = {x: F.rand(rng) for x in D}
for i, a in enumerate(A):
    for b in A[:i]:
        w[a ^ b] = F.mul(a, b)
T = len(A) - 1
inp = " ".join(f"{x:x}" for x in D) + "\n" + " ".join(f"{w[x]:x}" for x in D) + "\n"
out = subprocess.run([binary, "profile", "64", "1b", str(n), "2", str(T)], input=inp, capture_output=True, text=True).stdout
print(f"N={N} n={n} k=2: Sidon set of size {len(A)}; lines by exact agreement (>= {T}): {out.strip()};"
      f" Johnson radius sqrt(n) = {n ** 0.5:.2f}")
