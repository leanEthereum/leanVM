"""Note 64, item 1: agreements of pairs of window-mixed codewords, cube window.

For each (m, N, k): sample mu, then (a) random pairs: the mean number of agreements should be n/q (no free
agreement for a random difference); (b) planted pairs: the difference vanishes on a Hamming ball of radius R with
fewer than k points, so the free agreements are exactly the interior (the ball of radius R - 1, plus accidents),
and the rest agree with probability 1/q each.
"""
import importlib.util, random, sys, os

spec = importlib.util.spec_from_file_location("lib64", os.path.join(os.path.dirname(__file__), "64_lib.py"))
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)

rng = random.Random(64)


def run(m, N, k, pairs):
    F, n, dirs = L.GF(m), 1 << N, list(range(N))
    pw = L.powers(F, n, k)
    mu = L.sample_mu(F, n, N + 1, rng)
    # (a) random pairs (by linearity: the mixed word of a random difference, count its zeros)
    tot = free = 0
    for _ in range(pairs):
        ev = L.evaluate(F, pw, [F.rand(rng) for _ in range(k)])
        cw = L.mix(F, mu, ev, dirs)
        tot += sum(1 for s in cw if s == 0)
        free += len(L.interior([v for v in range(n) if ev[v] == 0], N))
    # (b) planted: largest ball with fewer than k points
    R = max(r for r in range(N) if len(L.ball(N, 0, r)) < k)
    B = L.ball(N, 0, R)
    Z = L.vanishing(F, B)
    ptot = pfree = 0
    for _ in range(pairs):
        e = [F.rand(rng) for _ in range(k - len(B))]
        ev = L.evaluate(F, pw, L.poly_mul(F, Z, e))
        cw = L.mix(F, mu, ev, dirs)
        fr = len(L.interior([v for v in range(n) if ev[v] == 0], N))
        ptot += sum(1 for s in cw if s == 0)
        pfree += fr
    q = F.q
    intB = len(L.interior(B, N))
    print(f"q=2^{m} N={N} k={k}: random pairs mean agr {tot/pairs:.4f} (free {free/pairs:.4f}), predicted n/q = {n/q:.4f};"
          f" planted ball R={R} |B|={len(B)} int={intB}: mean agr {ptot/pairs:.4f} (free {pfree/pairs:.4f}),"
          f" predicted {intB + (n-intB)/q:.4f}")


if __name__ == "__main__":
    pairs = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    for m in (8, 16):
        for N in (4, 5, 6):
            for k in ((1 << N) // 2, (1 << N) // 4):
                run(m, N, k, pairs)
