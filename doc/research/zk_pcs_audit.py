"""Mixed-field algebraic audit of the WHIR wire schedule, excluding hashes and FS.

The schedule follows python-verifier/verifier.py: boundary messages and separate
OOD/query introduction polynomials are exposed before batching. Small shapes
exercise this schedule; they are not production security configurations.
"""

import argparse
import importlib.util
import sys
from pathlib import Path
from random import Random

from zk_padding_experiments import Field


def verifier_module():
    path = Path(__file__).resolve().parents[2] / "python-verifier" / "verifier.py"
    spec = importlib.util.spec_from_file_location("leanvm_reference_verifier", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class Tower:
    def __init__(self, bits=8, verifier=None):
        self.bits = bits
        self.mask = (1 << bits) - 1
        self.base_mul = verifier._base_mul if bits == 64 else Field(bits, {2: 0b111, 4: 0x13, 8: 0x11B}[bits]).mul
        self.inverses, self.novel_cache = {}, {}

    def kmul(self, a, b):
        if not a or not b:
            return 0
        if a == 1:
            return b
        if b == 1:
            return a
        return self.base_mul(a, b) if self.bits == 64 else self.base_mul[a][b]

    def kinv(self, a):
        assert a
        if a in self.inverses:
            return self.inverses[a]
        original = a
        out, exponent = 1, (1 << self.bits) - 2
        while exponent:
            if exponent & 1:
                out = self.kmul(out, a)
            a = self.kmul(a, a)
            exponent >>= 1
        self.inverses[original] = out
        return out

    def coords(self, a):
        return tuple((a >> (i * self.bits)) & self.mask for i in range(3))

    def mul(self, a, b):
        if not a or not b:
            return 0
        if a == 1:
            return b
        if b == 1:
            return a
        aa, bb = self.coords(a), self.coords(b)
        p = [0] * 5
        for i in range(3):
            for j in range(3):
                p[i + j] ^= self.kmul(aa[i], bb[j])
        return (p[0] ^ p[3]) | ((p[1] ^ p[3] ^ p[4]) << self.bits) | ((p[2] ^ p[4]) << (2 * self.bits))

    def random(self, rng):
        return rng.getrandbits(3 * self.bits)

    def eq(self, point):
        values = [1]
        for r in point:
            values = [self.mul(1 ^ r, x) for x in values] + [self.mul(r, x) for x in values]
        return values

    def novel(self, log_size, query):
        assert query <= self.mask
        if (log_size, query) in self.novel_cache:
            return self.novel_cache[log_size, query]
        subspace = [1 << i for i in range(log_size + 1)]
        value, weights = query, [1]
        for j in range(log_size):
            root = subspace[j]
            normalized = self.kmul(value, self.kinv(root))
            weights += [self.kmul(x, normalized) for x in weights]
            value = self.kmul(value, value ^ root)
            for i in range(j + 1, log_size + 1):
                subspace[i] = self.kmul(subspace[i], subspace[i] ^ root)
        self.novel_cache[log_size, query] = tuple(weights)
        return tuple(weights)

    def expand(self, rows):
        return [[(a >> (j * self.bits)) & self.mask for a in row] for row in rows for j in range(3)]

    def pivots(self, rows, columns=None):
        selected = list(range(len(rows[0])) if columns is None else columns)
        rows = [[row[col] for col in selected] for row in rows]
        rows = [row for row in rows if any(row)]
        rank, pivots = 0, []
        for col in range(len(selected)):
            pivot = next((j for j in range(rank, len(rows)) if rows[j][col]), None)
            if pivot is None:
                continue
            rows[rank], rows[pivot] = rows[pivot], rows[rank]
            inverse = self.kinv(rows[rank][col])
            rows[rank] = [self.kmul(inverse, x) for x in rows[rank]]
            for j in range(rank + 1, len(rows)):
                factor = rows[j][col]
                if factor:
                    rows[j] = [a ^ self.kmul(factor, b) for a, b in zip(rows[j], rows[rank])]
            pivots.append(selected[col])
            rank += 1
        return pivots


class Audit:
    def __init__(self, field, log_size, folds, queries, rates=None, seed=0, query_mode="random"):
        assert 0 < sum(folds) < log_size
        assert len(folds) == len(queries)
        self.field, self.log_size, self.folds, self.queries = field, log_size, folds, queries
        self.rates = [1] * len(folds) if rates is None else rates
        self.rng, self.query_mode = Random(seed), query_mode
        self.order = list(range(log_size - folds[0], log_size)) + list(range(log_size - folds[0]))
        self.permutation = [sum(((i >> j) & 1) << bit for j, bit in enumerate(self.order)) for i in range(1 << log_size)]
        self.rows, self.labels = [], []
        self.challenges, self.query_points = [], []
        self.tape = []
        self.bound, self.factors = 0, [1] * (1 << log_size)

    def lift(self, weights, bound=None, factors=None):
        bound = self.bound if bound is None else bound
        factors = self.factors if factors is None else factors
        out = [0] * len(self.permutation)
        for i, original in enumerate(self.permutation):
            out[original] = self.field.mul(factors[i], weights[i >> bound])
        return out

    def emit(self, label, weights, bound=None, factors=None):
        self.labels.append(label)
        self.rows.append(self.lift(weights, bound, factors))

    def quad(self, label, weights):
        at_zero = [w if i % 2 == 0 else 0 for i, w in enumerate(weights)]
        quadratic = [weights[i & ~1] ^ weights[i | 1] for i in range(len(weights))]
        self.emit(label + ":h0", at_zero)
        self.emit(label + ":h2", quadratic)
        self.tape.append(("quad", (len(self.rows) - 2, len(self.rows) - 1, self.lift(weights))))

    def fold(self, weights, r):
        for i in range(len(self.factors)):
            self.factors[i] = self.field.mul(self.factors[i], r if (i >> self.bound) & 1 else 1 ^ r)
        self.bound += 1
        return [a ^ self.field.mul(r, a ^ b) for a, b in zip(weights[::2], weights[1::2])]

    def run(self, initial_weights=None):
        f = self.field
        self.initial_point = [f.random(self.rng) for _ in range(self.log_size)]
        weights = f.eq(self.initial_point) if initial_weights is None else [initial_weights[i] for i in self.permutation]
        self.emit("input-claim", weights)
        self.quad("initial", weights)
        for level, count in enumerate(self.folds):
            before_bound, before_factors = self.bound, self.factors[:]
            for j in range(count):
                challenge = f.random(self.rng)
                self.challenges.append(challenge)
                self.tape.append(("sample", challenge))
                weights = self.fold(weights, challenge)
                self.quad(f"L{level}:fold{j}", weights)
            remaining, length = self.log_size - self.bound, len(weights)
            final = level + 1 == len(self.folds)
            if final:
                start = len(self.rows)
                for i in range(length):
                    self.emit(f"final:{i}", [int(j == i) for j in range(length)])
                self.tape.append(("scalars", list(range(start, len(self.rows)))))
            else:
                self.tape.append(("root", (0, 0)))
                ood_point = [f.random(self.rng) for _ in range(remaining)]
                self.tape.extend(("sample", r) for r in ood_point)
                ood = f.eq(ood_point)
                self.emit(f"L{level}:ood-value", ood)
                self.tape.append(("scalar", len(self.rows) - 1))
                self.quad(f"L{level}:ood-intro", ood)
            domain = 1 << (remaining + self.rates[level])
            assert domain <= 1 << f.bits
            points = [self.rng.randrange(domain) for _ in range(self.queries[level])]
            if self.query_mode == "zero":
                points = [0] * len(points)
            elif self.query_mode == "prefix":
                points = [i % domain for i in range(len(points))]
            elif self.query_mode == "small-subspace":
                points = [self.rng.randrange(min(domain, 4)) for _ in points]
            self.query_points.append(points)
            self.tape.append(("queries", points))
            lam, power = f.random(self.rng), 1
            self.tape.append(("sample", lam))
            induced = [0] * length
            opened = []
            for q, point in enumerate(points):
                novel = f.novel(remaining, point)
                start = len(self.rows)
                for lane in range(1 << count):
                    lane_weights = [novel[i >> count] if i % (1 << count) == lane else 0 for i in range(length << count)]
                    self.emit(f"L{level}:query{q}:lane{lane}", lane_weights, before_bound, before_factors)
                opened.append(list(range(start, len(self.rows))))
                induced = [a ^ f.mul(power, b) for a, b in zip(induced, novel)]
                power = f.mul(power, lam)
            self.tape.append(("merkle", (level, opened)))
            self.quad(f"L{level}:query-intro", induced)
            if not final:
                weights = [a ^ f.mul(lam, b) ^ f.mul(f.mul(lam, lam), c) for a, b, c in zip(weights, ood, induced)]
            else:
                weights = [a ^ f.mul(lam, b) for a, b in zip(weights, induced)]
                for j in range(remaining):
                    challenge = f.random(self.rng)
                    self.tape.append(("sample", challenge))
                    weights = self.fold(weights, challenge)
                    if j + 1 < remaining:
                        self.quad(f"closing:{j}", weights)
        return self

    def padding(self, slack=0, replicate_initial=True):
        positions, bound = set(), 0
        for count, queries in zip(self.folds, self.queries):
            length = 1 << (self.log_size - bound - count)
            replicas = range(1 << self.folds[0]) if bound and replicate_initial else (0,)
            for tail in range(min(length, queries + slack)):
                for lane in range(1 << count):
                    for replica in replicas:
                        index = replica | (lane << bound) | (tail << (bound + count))
                        positions.add(self.permutation[index])
            bound += count
        return sorted(positions)


def kdot(field, left, right):
    out = 0
    for a, b in zip(left, right):
        out ^= field.kmul(a, b)
    return out


def edot(field, left, right):
    out = 0
    for a, b in zip(left, right):
        out ^= field.mul(a, b)
    return out


class RightInverse:
    def __init__(self, field, matrix):
        self.field, self.width = field, len(matrix[0])
        self.columns = field.pivots(matrix)
        size = len(matrix)
        assert len(self.columns) == size, "observation map is not onto"
        rows = [[row[col] for col in self.columns] + [int(i == j) for j in range(size)] for i, row in enumerate(matrix)]
        for i in range(size):
            pivot = next(j for j in range(i, size) if rows[j][i])
            rows[i], rows[pivot] = rows[pivot], rows[i]
            inverse = field.kinv(rows[i][i])
            rows[i] = [field.kmul(inverse, x) for x in rows[i]]
            for j in range(size):
                factor = rows[j][i]
                if j != i and factor:
                    rows[j] = [a ^ field.kmul(factor, b) for a, b in zip(rows[j], rows[i])]
        self.inverse = [row[size:] for row in rows]

    def solve(self, target):
        result = [0] * self.width
        for column, row in zip(self.columns, self.inverse):
            result[column] = kdot(self.field, row, target)
        return result


def envelope_translation(audit, difference):
    """Translate padding to cancel a real difference in the sufficient envelope.

    The envelope consists of every L0 query answer, every lane's column MLE,
    and the entire first-folded table. A translation is a bijection of uniform
    padding, so annihilating this envelope certifies identical conditional views.
    """
    field, k = audit.field, audit.folds[0]
    length, lanes = 1 << (audit.log_size - k), 1 << k
    prefix = 5 * (1 << audit.queries[0].bit_length())
    assert k >= 3 and prefix < length
    alpha = field.eq(audit.challenges[:k])
    phi = field.eq(audit.initial_point[k:])
    observations = [list(field.novel(audit.log_size - k, q)) for q in sorted(set(audit.query_points[0]))]
    observations += [[(a >> (j * field.bits)) & field.mask for a in phi] for j in range(3)]
    row_inverse = RightInverse(field, [row[:prefix] for row in observations])
    lane_matrix = [[field.coords(alpha[lane])[j] for lane in range(5)] for j in range(3)]
    lane_inverse = RightInverse(field, lane_matrix)
    original = [difference[lane * length : (lane + 1) * length] for lane in range(lanes)]
    adjusted = [row[:] for row in original]
    for row in adjusted:
        target = [kdot(field, weight, row) for weight in observations]
        correction = row_inverse.solve(target)
        for i, value in enumerate(correction):
            row[i] ^= value
    folded = [edot(field, alpha, [row[i] for row in adjusted]) for i in range(length)]
    for i, value in enumerate(folded):
        correction = lane_inverse.solve(field.coords(value))
        for lane, x in enumerate(correction):
            adjusted[lane][i] ^= x
    for lane, row in enumerate(adjusted):
        assert all(kdot(field, weight, row) == 0 for weight in observations)
        if lane >= 5:
            assert row[prefix:] == original[lane][prefix:]
    assert all(edot(field, alpha, [row[i] for row in adjusted]) == 0 for i in range(length))
    return [x for row in adjusted for x in row]


def envelope_certificate(verifier, bits=64):
    field = Tower(bits, verifier)
    for mode in ("random", "zero", "prefix", "small-subspace"):
        audit = Audit(field, 9, (4, 2), (3, 3), seed=17, query_mode=mode).run()
        rng = Random(19)
        difference = [rng.getrandbits(bits) if i // 32 >= 5 and i % 32 >= 20 else 0 for i in range(512)]
        translated = envelope_translation(audit, difference)
        assert any(translated[i] for i in range(512) if i // 32 >= 5 and i % 32 >= 20)
        assert all(edot(field, row, translated) == 0 for row in audit.rows)
        print(f"Envelope coupling K=2^{bits}, mode={mode}: padding-only translation cancels every audited wire observation", flush=True)


def five_direction_certificate():
    field, base_size, size = Tower(2), 4, 64
    failures = 0
    for t0 in range(size):
        if t0 == 1:
            continue
        for t1 in range(size):
            if t1 == 1:
                continue
            first = [1, t0, t1, field.mul(t0, t1)]
            span = {0}
            for value in first:
                span = {a ^ field.mul(b, value) for a in span for b in range(base_size)}
            assert len(span) == (64 if t0 >= 4 and t1 >= 4 else 4 if t0 < 4 and t1 < 4 else 16)
            for t2 in range(size):
                if t2 != 1 and len(span) < 64 and (len(span) == 4 or t2 in span):
                    failures += 1
    expected = (base_size - 1) ** 2 * (size - 1) + 2 * (base_size - 1) * (size - base_size) * (base_size**2 - 1)
    assert failures == expected
    assert failures * size <= 3 * (size - 1) ** 3
    print(f"Five-direction span: exhaustive K=GF(4), E=GF(64) failure count {failures}/{(size - 1) ** 3}, below 3/|E|", flush=True)


def reference_replay(verifier, basis_factory=None):
    """Exercise the actual verifier's algebra, with authentication checks stubbed."""
    field = Tower(64, verifier)
    audit = Audit(field, 6, (2, 1, 1), (2, 2, 2), seed=5, query_mode="prefix")
    rng = Random(6)
    message = [rng.getrandbits(64) for _ in range(64)]
    ext = lambda value: verifier.E(*field.coords(value))
    if basis_factory is None:
        audit.run()
        basis = lambda point: verifier.eq_eval([ext(r) for r in audit.initial_point], [point[i] for i in audit.order])
    else:
        basis = basis_factory(verifier, message)
        boolean = lambda i: [verifier.E((i >> j) & 1) for j in range(audit.log_size)]
        audit.run([int(basis(boolean(i))) for i in range(len(message))])
    values = [edot(field, row, message) for row in audit.rows]

    class Replay:
        cursor = 0

        def pop(self, kind):
            actual, value = audit.tape[self.cursor]
            self.cursor += 1
            assert kind == actual, (kind, actual, self.cursor)
            return value

        def sample(self):
            return ext(self.pop("sample"))

        def samples(self, count):
            return [self.sample() for _ in range(count)]

        def next_scalar(self):
            return ext(values[self.pop("scalar")])

        def next_scalars(self, count):
            if audit.tape[self.cursor][0] == "root":
                result = [ext(value) for value in self.pop("root")]
            else:
                result = [ext(values[i]) for i in self.pop("scalars")]
            assert len(result) == count
            return result

        def sumcheck_round_poly(self, size, claim):
            assert size == 3
            h0, h2, target = self.pop("quad")
            assert int(claim) == edot(field, target, message)
            return [ext(values[h0]), claim + ext(values[h2]), ext(values[h2])]

        def grind_check(self, bits):
            assert bits == verifier.QUERY_GRINDING_BITS

        def merkle(self, root, block_length, queries, width):
            level, opened = self.pop("merkle")
            assert queries == audit.query_points[level]
            result = []
            for row in opened:
                if level == 0:
                    words = [verifier.K(values[i]) for i in reversed(row)]
                else:
                    words = [verifier.K(c) for i in row for c in field.coords(values[i])]
                assert len(words) == width
                result.append(tuple(words))
            return result

    old_config, old_queries = verifier.derive_config, verifier.sample_queries
    verifier.derive_config = lambda *_: verifier.WhirConfig(tuple(audit.rates), audit.folds, audit.queries)
    verifier.sample_queries = lambda transcript, *_: transcript.pop("queries")
    replay = Replay()
    try:
        verifier.verify_whir(
            replay,
            audit.log_size,
            1,
            ext(values[0]),
            verifier.Digest(bytes(32)),
            basis,
        )
        assert replay.cursor == len(audit.tape)
    finally:
        verifier.derive_config, verifier.sample_queries = old_config, old_queries
    print("Reference replay: Python WHIR algebra accepts the complete generated transcript; Merkle/PoW checks are stubbed", flush=True)


def arithmetic_checks(verifier):
    field, rng = Tower(64, verifier), Random(42)
    for _ in range(30):
        a, b = field.random(rng), field.random(rng)
        aa, bb = verifier.E(*field.coords(a)), verifier.E(*field.coords(b))
        assert field.mul(a, b) == int(aa * bb)
    small = Tower()
    from zk_joint_experiments import novel_weights

    base = Field(8, 0x11B)
    for log_size in range(1, 7):
        for point in (0, 1, 3, 17, 127):
            assert list(small.novel(log_size, point)) == novel_weights(base, log_size, point)
    print("Arithmetic: actual K/E multiplication matches the Python verifier; novel basis matches independent product construction", flush=True)


def experiment(bits, verifier, log_size, folds, queries, trials):
    field = Tower(bits, verifier)
    for mode in ("random", "zero", "prefix", "small-subspace"):
        for seed in range(trials):
            audit = Audit(field, log_size, folds, queries, seed=seed, query_mode=mode).run()
            matrix = field.expand(audit.rows)
            full = len(field.pivots(matrix))
            results = []
            for slack in (0, 4, 8, 12):
                padding = audit.padding(slack)
                rank = len(field.pivots(matrix, padding))
                results.append((slack, len(padding), rank))
            print(f"K=2^{bits}, N={1 << log_size}, mode={mode}, seed={seed}, full={full}, (slack,masks,rank)={results}", flush=True)


def production_geometry(verifier):
    for log_size in (15, 20, 24, 28):
        config = verifier.derive_config(log_size, 1)
        remaining, rows = log_size, 0
        for level, (fold, count) in enumerate(zip(config.folds, config.queries)):
            remaining -= fold
            rows += (1 if level == 0 else 3) * (1 << fold) * count
        print(
            f"Production logN={log_size}: folds={config.folds}, queries={config.queries}, raw-query K coordinates={rows}, final coefficients={1 << remaining}",
            flush=True,
        )
        height, lanes = 1 << (log_size - config.folds[0]), 1 << config.folds[0]
        prefix = 5 * (1 << config.queries[0].bit_length())
        if prefix < height:
            masks = 5 * height + (lanes - 5) * prefix
            print(f"  Envelope construction: prefix={prefix}, masks={masks}, real capacity={(1 << log_size) - masks}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--actual-field", action="store_true")
    parser.add_argument("--envelope", action="store_true")
    parser.add_argument("--trials", type=int, default=2)
    args = parser.parse_args()
    verifier = verifier_module()
    arithmetic_checks(verifier)
    reference_replay(verifier)
    five_direction_certificate()
    production_geometry(verifier)
    if args.envelope:
        envelope_certificate(verifier, 64 if args.actual_field else 8)
    elif args.actual_field:
        experiment(64, verifier, 6, (2, 1, 1), (2, 2, 2), 1)
    else:
        experiment(8, verifier, 8, (2, 2, 1), (3, 3, 3), args.trials)
