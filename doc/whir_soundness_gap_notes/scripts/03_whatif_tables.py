#!/usr/bin/env python3
"""What-if tables for note 03: budgets, grinding costs, queries and opening size on the mu = 30 ladder.

Pure python, a few seconds. The model:
  - ladder of `derive_config` at log_n = 30: folds [6,4,4,4,4,4], kappa = [24,20,16,12,8,4],
    rate exponents R + [0,3,6,9,12,15], n_i = 2^(kappa_i + R_i);
  - a level at relative threshold tau takes t = ceil(108 / log2(1/tau)) queries (125 bits, 17-bit grind);
    the deployed counts are one or two above this at the Johnson threshold (list slack, degree slack,
    the batching row sharing the query message);
  - opening size: per level, the distinct opened leaves (64 K words at level 0, 16 E values after), the
    positions, and the pruned Merkle siblings (32 bytes each), averaged over random query sets; plus the
    opening's stream scalars. Merkle hashes: Keccak-f permutations of the unpruned paths (leaf 4 or 2, node 1).
"""
import math, random, hashlib, time

random.seed(30)
LOG_E = 128
SEC = 125
G_FOLD, G_BATCH, G_OOD, G_QUERY = 7, 13, 15, 17
FOLDS = [6, 4, 4, 4, 4, 4]
KAPPA = [24, 20, 16, 12, 8, 4]
NU = [k + f for k, f in zip(KAPPA, FOLDS)]
RATE_STEP = [0, 3, 6, 9, 12, 15]
DEPLOYED = {1: [218, 55, 32, 23, 18, 15], 2: [109, 44, 28, 21, 17, 15], 3: [73, 37, 25, 19, 16, 15], 4: [55, 32, 23, 18, 16, 14]}
J0 = 512  # the search's row is (J0 + 1) L: 512 stacked claims and the ring switch's 2, less one


def pruned_siblings(height, positions):
    nodes = set(positions)
    total = 0
    for _ in range(height):
        total += sum(1 for p in nodes if (p ^ 1) not in nodes)
        nodes = {p >> 1 for p in nodes}
    return total


def opening(R, queries, trials=12):
    """(bytes, verifier Merkle permutations) of the Merkle part for the given per-level query counts."""
    size = perms = 0.0
    for i, t in enumerate(queries):
        h = KAPPA[i] + R + RATE_STEP[i]
        leaf = 512 if i == 0 else 256
        acc = 0
        for _ in range(trials):
            pos = [random.randrange(1 << h) for _ in range(t)]
            acc += len(set(pos)) * leaf + 32 * pruned_siblings(h, pos)
        size += acc / trials + 4 * t + 16
        perms += t * ((4 if i == 0 else 2) + h)
    return size, perms


STREAM = 16 * (26 * 5 + (2 + 6 + 3) + 4 * (2 + 4 + 3) + 2 + 1 + (16 + 4 + 1) + 4 * 2)


def t_of(bits):
    return math.ceil(108 / bits - 1e-9)


def johnson_bits(R, i):
    n = 1 << (KAPPA[i] + R + RATE_STEP[i])
    d = (1 << KAPPA[i]) - 1 + FOLDS[i]
    return 0.5 * math.log2(n / d)


def flats_cap(Ri, deep4=False):
    """Bits per query at the known-list frontier, for budgets 2^10 to 2^27 (note 01, section 4).

    Rate 1/2: the height-2 tree family, 2^29.4 at 5n/8. Lower rates: flats at 2 rho. With `deep4`, rates 2^-6 and
    below take 4 rho instead (the pigeonhole families of note 01, which exist when the domain is large enough)."""
    if Ri == 1:
        return math.log2(8 / 5)
    if deep4 and Ri >= 6:
        return Ri - 2
    return Ri - 1


def scenario(R, kind, theta=None, pole_cap=None):
    out = []
    for i in range(6):
        Ri = R + RATE_STEP[i]
        if kind == "johnson":
            bits = johnson_bits(R, i)
        elif kind == "theta":
            bits = min(theta * Ri, flats_cap(Ri))
        elif kind == "theta_nocap":
            bits = theta * Ri
        elif kind == "frontier":
            bits = flats_cap(Ri)
        elif kind == "frontier4":
            bits = flats_cap(Ri, deep4=True)
        elif kind == "frontier916":
            bits = math.log2(16 / 9) if Ri == 1 else Ri - 1
        elif kind == "capacity":
            bits = Ri
        if pole_cap is not None:
            bits = min(bits, pole_cap)
        bits = max(bits, johnson_bits(R, i)) if kind != "johnson" else bits
        out.append(t_of(bits))
    return out


print("== A. list budgets b (log2 of the largest list a message tolerates) under the present analysis")
print(f"   fold round, eps = 2 L / |E|, grind g_f:          b = g_f + 2            = {G_FOLD + 2} now")
print(f"   level-0 batching, eps = (J0 + 1) L / |E|, g_b:   b = g_b + 3 - log2 {J0 + 1}  = {G_BATCH + 3 - math.log2(J0 + 1):.2f} now")
for nu in (30, 24):
    b1 = (LOG_E - SEC + G_OOD + 1 - math.log2(nu)) / 2
    b2 = (2 * LOG_E - SEC + G_OOD + 1 - 2 * math.log2(nu)) / 2
    b20 = (2 * LOG_E - SEC + 0 + 1 - 2 * math.log2(nu)) / 2
    b3 = (3 * LOG_E - SEC + G_OOD + 1 - 3 * math.log2(nu)) / 2
    print(f"   OOD, eps = C(L,2) (nu/|E|)^s, nu = {nu}: b = {b1:.2f} (s = 1), {b2:.2f} (s = 2), {b20:.2f} (s = 2, no grind), {b3:.2f} (s = 3)")
for R in (1, 2, 3, 4):
    row = []
    for i in range(5):
        t = DEPLOYED[R][i]
        row.append(G_QUERY + 3 - 1 - math.log2(t + 1))
    print(f"   rate 2^-{R}: next level's batching in level i's query message, half the budget, (t+1) L <= 2^19: b = " + ", ".join(f"{x:.1f}" for x in row))

print()
print("== B. grinding a list budget 2^b costs (Keccak-f permutations per proof, mu = 30: 26 fold rounds, 6 OOD points, 6 query messages)")
now = 26 * 2**G_FOLD + 2**G_BATCH + 6 * 2**G_OOD + 6 * 2**G_QUERY
print(f"   now: 26*2^{G_FOLD} + 2^{G_BATCH} + 6*2^{G_OOD} + 6*2^{G_QUERY} = {now:,}")
t0 = time.time()
x = b"\0" * 64
for _ in range(200000):
    x = hashlib.sha3_256(x).digest()
rate = 200000 / (time.time() - t0)
print(f"   (hashlib sha3_256 on this machine, one core, scalar: {rate/1e6:.2f} M permutations/s; a prover's multi-way search is faster)")
print("   b | g_f = b-2 | fold perms | g_b power batching (b+7) | g_b split OOD coefficient (b-2) | total with split, 2 OOD points no OOD grind | x now | core-seconds")
for b in (7, 9, 10, 12, 14, 16, 18, 20, 22, 24, 26, 30, 40):
    gf = max(b - 2, 0)
    fold = 26 * 2**gf
    gb_pow = b + 7
    gb_split = max(b - 2, 10)
    total = fold + 2**gb_split + 6 * 2**G_QUERY
    print(f"  {b:2d} | {gf:2d} | {fold:.3g} | {gb_pow} ({2**gb_pow:.3g}) | {gb_split} ({2**gb_split:.3g}) | {total:.3g} | {total/now:.2f} | {total/rate:.3g}")

print()
print("== C. queries, verifier Merkle permutations and opening size on the mu = 30 ladder")
print(f"   (stream scalars of the opening: {STREAM} bytes, included)")
for R in (1, 2, 3, 4):
    print(f"-- level-0 rate 2^-{R}; rate exponents {[R + s for s in RATE_STEP]}; log2 n = {[KAPPA[i] + R + RATE_STEP[i] for i in range(6)]}")
    rows = [("deployed", DEPLOYED[R]), ("Johnson, no slack", scenario(R, "johnson"))]
    for th in (0.6, 0.7, 0.8, 0.9):
        rows.append((f"tau = rho^{th}, capped by known lists", scenario(R, "theta", th)))
    rows.append(("known-list frontier (flats 2 rho; 5/8 at rate 1/2)", scenario(R, "frontier")))
    rows.append(("  same, 4 rho at rates <= 2^-6", scenario(R, "frontier4")))
    rows.append(("  same, bits/query <= 10 (coset pole, g_f = 7)", scenario(R, "frontier", pole_cap=10)))
    rows.append(("  frontier with 9/16 at rate 1/2 (budget 2^30 up)", scenario(R, "frontier916")))
    for th in (0.7, 0.8, 0.9):
        rows.append((f"tau = rho^{th}, lists irrelevant", scenario(R, "theta_nocap", th)))
    rows.append(("capacity", scenario(R, "capacity")))
    base = None
    for name, q in rows:
        size, perms = opening(R, q)
        size += STREAM
        if base is None:
            base = (sum(q), perms, size)
        print(f"   {name:52s} t = {str(q):28s} sum {sum(q):4d}  perms {perms:7.0f} ({perms/base[1]:.2f})  {size/1024:6.1f} KiB ({size/base[2]:.2f})")

print()
print("== D. level 0 alone: queries at a relative threshold tau")
for R in (1, 2, 3, 4):
    rho = 2.0**-R
    taus = sorted({round(x, 4) for x in [rho**0.5, rho**0.6, rho**0.7, rho**0.8, rho**0.9, 2 * rho if R > 1 else 9 / 16, 0.628 if R == 1 else rho * 1.5, 0.625 if R == 1 else 0.152 if R == 4 else rho, rho]}, reverse=True)
    print(f"   rate 2^-{R}: " + ", ".join(f"tau {t:.4f}: {t_of(-math.log2(t))}" for t in taus))

print()
print("== E. m-fold OOD collisions: worst-case structure (Markov) against a generic list, L = 2^26, nu = 30, one OOD point")
L = 2.0**26
pair = L * (L - 1) / 2 * 30 / 2.0**128
for m in (2, 3, 4, 2**13):
    markov = pair / (m * (m - 1) / 2)
    generic = math.exp(math.lgamma(L + 1) - math.lgamma(m + 1) - math.lgamma(L - m + 1) + (m - 1) * math.log(30 / 2.0**128)) if m < 10 else 0
    print(f"   m = {m}: Pr <= 2^{math.log2(markov):.1f} (Markov), about 2^{math.log2(generic) if generic else float('-inf'):.1f} generic; stage cost 2^{G_OOD - math.log2(markov):.1f} hashes at best, gain {m}x on the next escape")

print()
print("== F. level 0 at mu = 30 (kappa = 24): flats and coset unions only (note 01 has larger families at rates 1/2 and 1/4: use its table), and the floor they put on t as a function of the list budget b")


def lg_binom(n, k):
    return (math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)) / math.log(2)


def families(R):
    fams = []
    if R >= 2:
        N = 24 + R
        lg = sum(math.log2(2.0 ** (N - i) - 1) - math.log2(2.0 ** (R - 1 - i) - 1) for i in range(R - 1))
        fams.append((2.0 ** (1 - R), lg, f"flats codim {R - 1}"))
    for j in range(R, 13):
        M = 1 << j
        base = M >> R
        if base + 2 >= M:
            continue
        fams.append(((base + 1) / M, lg_binom(M, base + 1), f"cosets M={M} m={base + 1}"))
        fams.append(((base + 2) / M, lg_binom(M, base + 2) - j, f"cosets M={M} m={base + 2}, e_1 pinned"))
    return fams


for R in (1, 2, 3, 4):
    fams = families(R)
    line = []
    for b in (7, 9, 12, 16, 20, 24, 27, 52, 77):
        over = [f for f in fams if f[1] > b and f[0] <= 2.0 ** (-R / 2)]
        tau, lg, name = max(over)
        line.append(f"b={b}: t>={t_of(-math.log2(tau))} ({name}, 2^{lg:.1f} at {tau:.4f})")
    print(f"   rate 2^-{R} (deployed {DEPLOYED[R][0]}): " + "; ".join(line))

print()
print("== G. lowering level 0 only (later levels as deployed): opening size")
for R, t0s in ((1, (218, 181, 171, 160, 131)), (2, (109, 108, 77)), (3, (73, 61, 54)), (4, (55, 46, 40, 36))):
    base = None
    for t0 in t0s:
        q = [t0] + DEPLOYED[R][1:]
        size, perms = opening(R, q)
        size += STREAM
        base = base or (perms, size)
        print(f"   rate 2^-{R}: t = {q}: perms {perms:.0f} ({perms/base[0]:.2f}), {size/1024:.1f} KiB ({size/base[1]:.2f})")
print("   fold grinding at level 0 only: 6 * 2^g_f permutations: " + ", ".join(f"b={b}: {6 * 2**(b-2):.3g}" for b in (12, 16, 20, 24, 27)))
