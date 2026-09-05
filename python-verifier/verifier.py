from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from functools import cache, reduce
from itertools import accumulate, islice, repeat
from operator import mul
from pathlib import Path
from struct import pack, unpack


class VerificationError(Exception):
    """Invalid proof."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


# Field arithmetic ------------------------------------------------------------


def _base_mul(left: int, right: int) -> int:
    product = 0
    while right:
        if right & 1:
            product ^= left
        right >>= 1
        left <<= 1
    low, high = product & (2**64 - 1), product >> 64
    folded = low ^ high ^ (high << 1) ^ (high << 3) ^ (high << 4)
    overflow = folded >> 64
    return ((folded & (2**64 - 1)) ^ overflow ^ (overflow << 1) ^ (overflow << 3) ^ (overflow << 4)) & (2**64 - 1)


@dataclass(frozen=True, slots=True)
class K:
    """GF(2^64) = F2[x]/(x^64 + x^4 + x^3 + x + 1)"""

    value: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.value, int) or isinstance(self.value, bool) or not 0 <= self.value <= (2**64 - 1):
            raise ValueError("a K element is a 64-bit unsigned integer")

    def __index__(self) -> int:
        return self.value

    def to_bytes(self) -> bytes:
        """Its transport image: one 64-bit little-endian word."""
        return self.value.to_bytes(8, "little")

    def __bool__(self) -> bool:
        return bool(self.value)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, K):
            return self.value == other.value
        return isinstance(other, int) and not isinstance(other, bool) and self.value == other

    def __hash__(self) -> int:
        return hash(self.value)

    def __add__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(self.value ^ rhs.value)

    __radd__ = __add__

    def __mul__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(_base_mul(self.value, rhs.value))

    __rmul__ = __mul__

    def __repr__(self) -> str:
        return f"K(0x{self.value:016x})"


def _as_k(value: object) -> K | None:
    if isinstance(value, K):
        return value
    if isinstance(value, int) and not isinstance(value, bool) and 0 <= value <= 2**64 - 1:
        return K(value)
    return None


@dataclass(frozen=True, slots=True, init=False)
class E:
    """K[y]/(y^3 + y + 1): the challenge field, a degree-3 extension of K. Limbs may be given as plain integers, which are lifted."""

    c0: K
    c1: K
    c2: K

    def __init__(self, c0: K | int = 0, c1: K | int = 0, c2: K | int = 0) -> None:
        object.__setattr__(self, "c0", c0 if isinstance(c0, K) else K(c0))
        object.__setattr__(self, "c1", c1 if isinstance(c1, K) else K(c1))
        object.__setattr__(self, "c2", c2 if isinstance(c2, K) else K(c2))

    @classmethod
    def from_bytes(cls, data: bytes) -> E:
        require(len(data) == 24, "a field element must contain exactly 24 bytes")
        return cls(*unpack("<3Q", data))

    def to_bytes(self) -> bytes:
        return pack("<3Q", self.c0, self.c1, self.c2)

    @staticmethod
    def lift(value: object) -> E:
        """`value` as an extension element; anything that is not one is an error."""
        if isinstance(value, E):
            return value
        lifted = _as_k(value)
        if lifted is not None:
            return E(lifted)
        raise TypeError(f"cannot use {type(value).__name__} as a field element")

    @staticmethod
    def sum(values: Iterable[E]) -> E:
        return sum(values, ZERO)

    def __int__(self) -> int:
        return self.c0.value | self.c1.value << 64 | self.c2.value << 128

    def __bool__(self) -> bool:
        return bool(self.c0 or self.c1 or self.c2)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, E):
            return self.c0 == other.c0 and self.c1 == other.c1 and self.c2 == other.c2
        return not (self.c1 or self.c2) and self.c0 == other

    def __hash__(self) -> int:
        return hash(int(self))

    def __add__(self, other: object) -> E:
        rhs = self.lift(other)
        return E(self.c0 + rhs.c0, self.c1 + rhs.c1, self.c2 + rhs.c2)

    __radd__ = __add__

    def __mul__(self, other: object) -> E:
        rhs = self.lift(other)
        # y^3 = y + 1 folds the degree-4 product back into three limbs.
        p0 = self.c0 * rhs.c0
        p1 = self.c0 * rhs.c1 + self.c1 * rhs.c0
        p2 = self.c0 * rhs.c2 + self.c1 * rhs.c1 + self.c2 * rhs.c0
        p3 = self.c1 * rhs.c2 + self.c2 * rhs.c1
        p4 = self.c2 * rhs.c2
        return E(p0 + p3, p1 + p3 + p4, p2 + p4)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> E:
        if exponent < 0:
            return self.inv() ** -exponent
        base, out, n = self, ONE, exponent
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def inv(self) -> E:
        require(bool(self), "division by zero in GF(2^192)")
        return self ** (2**192 - 2)

    def __truediv__(self, other: object) -> E:
        rhs = self.lift(other)
        return self * rhs.inv()

    def __repr__(self) -> str:
        return f"E(0x{self.c2.value:016x}{self.c1.value:016x}{self.c0.value:016x})"


ZERO = E(0)
ONE = E(1)
GEN = E(2)
Y = E(0, 1)  # the tower generator, y^3 = y + 1


def powers(base: E, count: int) -> list[E]:
    """`[1, base, base^2, ...]`, `count` terms."""
    return list(islice(accumulate(repeat(base), mul, initial=ONE), count))


# BLAKE2s and digests ---------------------------------------------------------

BLAKE2S_IV = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)  # fmt: skip
BLAKE2S_SIGMA = ((0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15), (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3), (11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4), (7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8), (9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13), (2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9), (12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11), (13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10), (6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5), (10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0))  # fmt: skip
BLAKE2S_G_LANES = ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14))  # fmt: skip


def blake2s_hash(data: bytes) -> Digest:
    """Standard 32-byte unkeyed BLAKE2s-256 hash."""
    return Digest(hashlib.blake2s(data).digest())


@dataclass(frozen=True, slots=True)
class Digest:
    """256 bits"""

    value: bytes

    def __post_init__(self) -> None:
        require(len(self.value) == 32, "a digest is 256 bits")

    def words(self) -> tuple[int, int, int, int]:
        """Its four 64-bit words, the form the compression chain runs in."""
        return unpack("<4Q", self.value)

    def halves(self) -> tuple[E, E]:
        """Its two 128-bit halves, the one form a digest travels in."""
        w0, w1, w2, w3 = self.words()
        return (E(w0, w1), E(w2, w3))

    @classmethod
    def from_halves(cls, low: E, high: E) -> Digest:
        require(not (low.c2 or high.c2), "a digest half is 128-bit")
        return cls(pack("<4Q", low.c0, low.c1, high.c0, high.c1))


# Multilinear and stacking helpers --------------------------------------------


type MultilinearPoint = tuple[E, ...]


def eq_kernel(point: Sequence[E]) -> list[E]:
    out = [ONE]
    for r in point:
        out = [v * (ONE + r) for v in out] + [v * r for v in out]
    return out


def multilinear_eval(mle: Sequence[K | E], point: Sequence[E]) -> E:
    require(len(mle) == 2 ** len(point), "multilinear table has the wrong size")
    cur = [E.lift(value) for value in mle]
    for r in point:
        cur = [cur[2 * i] * (ONE + r) + cur[2 * i + 1] * r for i in range(len(cur) // 2)]
    return cur[0]


def log2_ceil(value: int) -> int:
    return max(0, (value - 1).bit_length())


def log2_strict(value: int) -> int:
    require(value > 0 and not value & (value - 1), "expected a power of two")
    return value.bit_length() - 1


def eq_eval(left: Sequence[E], right: Sequence[E]) -> E:
    result = ONE
    for x, y in zip(left, right, strict=True):
        result *= ONE + x + y
    return result


def dot(left: Sequence[K | E], right: Sequence[K | E]) -> E:
    result = ZERO
    for x, y in zip(left, right, strict=True):
        result += E.lift(x) * y
    return result


def index_mle(point: MultilinearPoint) -> E:
    """MLE of ``[1, g, g^2, ...]`` at an LSB-first point."""
    result = ONE
    generator_power = GEN
    for challenge in point:
        result *= ONE + challenge * (ONE + generator_power)
        generator_power **= 2
    return result


def poly_eval(coefficients: Sequence[E], point: E) -> E:
    """A polynomial at `point`, by Horner over its coefficients, constant first."""
    return reduce(lambda acc, c: acc * point + c, reversed(coefficients), ZERO)


@dataclass(frozen=True)
class Placement:
    """Where something sits in the stacked cube: a claim's point fills the `variables` coordinates above `low`, the bits of `index` fixing the rest.
    `low` is zero for a block with a cube of its own, and the slot width for a column interleaved into a bigger block."""

    variables: int
    index: int
    low: int = 0

    def stack_point(self, point: MultilinearPoint, stack_log: int) -> MultilinearPoint:
        bits = _selector_point(self.index, stack_log)
        return bits[: self.low] + tuple(point) + bits[self.low + self.variables :]

    def eq_above(self, point: Sequence[E]) -> E:
        """eq weight of the coordinates above the window."""
        bits = _selector_point(self.index >> (self.low + self.variables), len(point) - self.low - self.variables)
        return eq_eval(bits, point[self.low + self.variables :])


def stack_offsets(sizes: Sequence[int]) -> tuple[list[int], int]:
    offsets = [0] * len(sizes)
    total = 0
    for index, size in sorted(enumerate(sizes), key=lambda item: (-item[1], item[0])):
        offsets[index] = total
        total += 2**size
    return offsets, log2_ceil(total)


def _selector_point(selector: int, length: int) -> MultilinearPoint:
    return tuple(E(selector >> bit & 1) for bit in range(length))


# Proof transport ------------------------------------------------------------


@dataclass(frozen=True)
class Proof:
    stream: tuple[E, ...]
    merkle_openings: bytes

    @classmethod
    def load(cls, stream: Path, merkle_openings: Path) -> Proof:
        data = stream.read_bytes()
        require(len(data) % 24 == 0, "the stream is not a whole number of field elements")
        return cls(tuple(E.from_bytes(data[at : at + 24]) for at in range(0, len(data), 24)), merkle_openings.read_bytes())


# Fiat--Shamir ---------------------------------------------------------------

DS_OBSERVE = 1
DS_SQUEEZE = 2
DS_POW_BASE = 3
DS_POW_NONCE = 4


def compress(left: Sequence[K | int], right: Sequence[K | int]) -> tuple[int, int, int, int]:
    """Hash two four-word operands, a word being a plain integer or the K element standing for it."""
    return unpack("<4Q", blake2s_hash(b"".join(int(x).to_bytes(8, "little") for x in (*left, *right))).value)


class Transcript:
    def __init__(self, proof: Proof, fiat_shamir_IV: Digest, public_input: Digest) -> None:
        self.proof = proof
        self.state = compress(fiat_shamir_IV.words(), public_input.words())
        self.stream_offset = 0  # in E field elements
        self.opening_offset = 0  # in bytes

    def observe(self, value: E) -> None:
        self.state = compress(self.state, (value.c0, value.c1, value.c2, DS_OBSERVE))

    def sample(self) -> E:
        self.state = compress(self.state, (0, 0, 0, DS_SQUEEZE))
        return E(*self.state[:3])

    def samples(self, count: int) -> list[E]:
        return [self.sample() for _ in range(count)]

    def _next(self) -> E:
        require(self.stream_offset < len(self.proof.stream), "proof stream exhausted")
        value = self.proof.stream[self.stream_offset]
        self.stream_offset += 1
        return value

    def next_scalar(self) -> E:
        value = self._next()
        self.observe(value)
        return value

    def next_scalars(self, count: int) -> list[E]:
        return [self.next_scalar() for _ in range(count)]

    def grind_check(self, bits: int) -> None:
        nonce = self._next()
        block = (nonce.c0, nonce.c1, nonce.c2, DS_POW_NONCE)
        digest = compress(compress(self.state, (0, 0, 0, DS_POW_BASE)), block)[0]
        valid = nonce == ZERO if bits == 0 else digest & (2**bits - 1) == 0
        self.state = compress(self.state, block)
        require(valid, "invalid grinding nonce")

    def _merkle_data(self, length: int) -> bytes:
        end = self.opening_offset + length
        require(end <= len(self.proof.merkle_openings), "Merkle opening missing")
        chunk = self.proof.merkle_openings[self.opening_offset : end]
        self.opening_offset = end
        return chunk

    def merkle(self, root: Digest, block_length: int, queries: Sequence[int], leaf_words: int) -> list[tuple[K, ...]]:
        height = log2_strict(block_length)
        rows = []
        for query in queries:
            leaf = self._merkle_data(8 * leaf_words)
            node = blake2s_hash(leaf)
            for level in range(height):
                sibling = self._merkle_data(32)
                left, right = (node.value, sibling) if query >> level & 1 == 0 else (sibling, node.value)
                node = blake2s_hash(left + right)
            require(node == root, "Merkle root mismatch")
            rows.append(tuple(K(word) for word in unpack(f"<{leaf_words}Q", leaf)))
        return rows

    def sumcheck_round_poly(self, count: int, claim: E, eq_factor: E | None = None) -> list[E]:
        """returns q(X) := c0 + c1X + c2X^2 + ..."""
        if eq_factor is None:
            constant, tail = self.next_scalar(), self.next_scalars(count - 2)  # `q(0) + q(1) == claim`. The transcript contains c0, c2, c3 ...
            return [constant, claim + E.sum(tail), *tail]
        # `(1 + r) q(0) + r q(1) == claim`. The transcript contains c1, c2, c3 ... (r := eq_factor)
        tail = self.next_scalars(count - 1)
        return [claim + eq_factor * E.sum(tail), *tail]

    def finish(self) -> None:
        require(self.stream_offset == len(self.proof.stream), "proof stream not fully consumed")
        require(self.opening_offset == len(self.proof.merkle_openings), "Merkle openings not fully consumed")


def sumcheck(transcript: Transcript, claim: E, count: int, equalities: Sequence[E | None]) -> tuple[MultilinearPoint, E]:
    point = []
    for equality in equalities:
        message = transcript.sumcheck_round_poly(count, claim, equality)
        challenge = transcript.sample()
        point.append(challenge)
        claim = poly_eval(message, challenge)
    return tuple(point), claim


# Bus balance and decomposition ---------------------------------------------


def verify_gkr_grand_products(depth: int, transcript: Transcript) -> tuple[E, MultilinearPoint, tuple[E, E, E]]:
    shared, count = transcript.next_scalar(), transcript.next_scalar()
    combiner = transcript.sample()
    point: list[E] = []
    values = (shared, shared, count)  # 3 grand product GKR are batched together: push, pull, count

    layer = depth
    while layer > 0:
        # Two levels a step. An odd depth starts with one.
        step = 1 if layer % 2 else 2
        claim = poly_eval(values, combiner)
        # The product is degree 2^step, so one more coefficient than that per round.
        x, claim = sumcheck(transcript, claim, 2**step + 1, point)

        children = [transcript.next_scalars(2**step) for _ in range(3)]
        products = [reduce(mul, child) for child in children]
        require(claim == poly_eval(products, combiner), f"GKR layer {layer}: children do not match the sumcheck")

        y = transcript.samples(step)
        values = [multilinear_eval(child, y) for child in children]
        combiner = transcript.sample()
        point = [*y, *x]
        layer -= step

    return count, tuple(point), (values[0], values[1], values[2])


@dataclass
class Form:
    """A polynomial of degree at most 2 in a table's columns."""

    terms: dict[tuple[int, ...], E] = field(default_factory=dict)  # monomial -> coefficient; () is 1, (i,) is x_i, (i, j) is x_i*x_j

    def add_scaled(self, other: Form, weight: E) -> None:
        for monomial, coefficient in other.terms.items():
            self.terms[monomial] = self.terms.get(monomial, ZERO) + weight * coefficient

    def __add__(self, other: Form) -> Form:
        combined = Form(dict(self.terms))
        combined.add_scaled(other, ONE)
        return combined

    @staticmethod
    def sum(forms: Iterable[Form]) -> Form:
        """`Σ forms`, the empty sum being the zero polynomial."""
        return sum(forms, Form())

    def evaluate(self, column: Callable[[int], E]) -> E:
        return E.sum(reduce(mul, map(column, monomial), c) for monomial, c in self.terms.items())


@dataclass(frozen=True)
class BusBlock:
    """One block of a bus side, always owned by a table. The three blocks no table owns are the framework, on `BusLayout`."""

    log_rows: int  # the owner's height: this block flushes 2^log_rows rows
    coordinates: tuple[Form, ...]  # the tuple flushed, over the owner's OWN local column indices; stays symbolic until its table sumcheck
    owner: int  # whose block it is, by opcode


@dataclass(frozen=True)
class BusLayout:
    """Where a side's blocks sit in the stacked leaf cube. Split by kind because framework coordinates are
    public, so the verifier evaluates their fingerprints outright, while a table's stay symbolic until its sumcheck."""

    depth: int  # log2 of the padded cube, so how many layers the side's GKR walks
    framework: tuple[Placement, ...]  # the blocks no table owns, stacked first: boundary state, memory, bytecode (none on the count side)
    tables: tuple[Placement, ...]  # one per block a table owns, in the side's own block order


FrameworkLogRows = tuple[int, int, int] | tuple[()]  # state, memory, bytecode


def bus_layout(framework_log_rows: FrameworkLogRows, blocks: Sequence[BusBlock]) -> BusLayout:
    sizes = [*framework_log_rows, *(block.log_rows for block in blocks)]
    offsets, depth = stack_offsets(sizes)
    placements = [Placement(size, offset) for size, offset in zip(sizes, offsets)]
    split = len(framework_log_rows)
    return BusLayout(depth, tuple(placements[:split]), tuple(placements[split:]))


@dataclass(frozen=True)
class ColumnClaim:
    column: int
    point: MultilinearPoint
    value: E

    def on_stack(self, layout: Layout) -> StackClaim:
        point = layout.placements[self.column].stack_point(self.point, layout.stack_log)
        return (lambda x: eq_eval(point, x), self.value)


BUS_BITS = 4  # bus communicates tuples of 2^BUS_BITS field elements


@dataclass(frozen=True)
class BusResult:
    claims: tuple[ColumnClaim, ...]
    point: MultilinearPoint  # the GKR point zeta, which the table sumcheck reuses
    forms: tuple[tuple[Form, ...], ...]  # forms[table][side]
    totals: tuple[E, E, E]  # what the tables owe each side, derived


def verify_bus_balance(layout: Layout, transcript: Transcript) -> BusResult:
    framework_log_rows = (0, layout.log_memory, layout.log_bytecode)  # state, memory, bytecode
    push_layout = bus_layout(framework_log_rows, layout.push)
    pull_layout = bus_layout(framework_log_rows, layout.pull)
    count_layout = bus_layout((), layout.count)

    alphas = transcript.samples(BUS_BITS)
    weights = eq_kernel(alphas)
    beta = transcript.sample()
    count_root, point, tree_values = verify_gkr_grand_products(push_layout.depth, transcript)
    require(count_root != ZERO, "a bus count is zero")

    # The framework blocks' committed columns, in the order the two sides first
    # name them: the memory image on push, then each array's final count on pull.
    memory_low = tuple(point[: layout.log_memory])
    bytecode_low = tuple(point[: layout.log_bytecode])
    memory = transcript.next_scalars(3)
    memory_final = transcript.next_scalar()
    bytecode_final = transcript.next_scalar()
    claims = [ColumnClaim(column, memory_low, memory[column]) for column in (MEMORY_0, MEMORY_1, MEMORY_2)]
    claims.append(ColumnClaim(MEMORY_FINAL_COUNTERS, memory_low, memory_final))
    claims.append(ColumnClaim(BYTECODE_FINAL_COUNTERS, bytecode_low, bytecode_final))

    def fingerprints(pc: E, memory_count: E, bytecode_count: E) -> tuple[E, E, E]:
        """The three framework tuples, each its coordinates weighted by eq(alpha, .); slots past the ones
        named are zero. A side differs only here: push seeds each array at count one, pull finalizes it
        with the committed final count and ends at the last pc. Both boundaries sit in frame 0."""
        return (
            dot(weights[:3], (SEP_STATE, pc, _gpow(0))),
            dot(weights[:6], (SEP_MEM, index_mle(memory_low), memory_count, *memory)),
            dot(weights[:3], (SEP_BYTECODE, index_mle(bytecode_low), bytecode_count)) + multilinear_eval(layout.bytecode, (*bytecode_low, *alphas)),
        )

    final_pc = _gpow(2**layout.log_bytecode - 1)  # the execution ends at the bytecode's last instruction
    sides = (
        (layout.push, push_layout, fingerprints(_gpow(0), ONE, ONE), weights, beta),
        (layout.pull, pull_layout, fingerprints(final_pc, memory_final, bytecode_final), weights, beta),
        (layout.count, count_layout, (), (ONE,), ZERO),  # The count channel owns no framework block and runs at alpha = beta = 0.
    )
    totals = []  # what remains to be proven by the next table sumcheck
    forms = tuple(tuple(Form() for _ in range(3)) for _ in TABLES)
    for side, (blocks, side_layout, framework_fingerprints, side_weights, side_beta) in enumerate(sides):
        framework_selectors = [p.eq_above(point) for p in side_layout.framework]
        table_selectors = [p.eq_above(point) for p in side_layout.tables]
        known = dot(framework_selectors, [side_beta + fingerprint for fingerprint in framework_fingerprints])
        # A table's blocks stay symbolic: they accumulate into the form its sumcheck settles over its own columns.
        beta_form = _const(side_beta)
        for selector, block in zip(table_selectors, blocks, strict=True):
            form = forms[block.owner][side]
            form.add_scaled(beta_form, selector)
            for slot, coordinate in enumerate(block.coordinates):
                form.add_scaled(coordinate, selector * side_weights[slot])  # the fingerprint, one tuple slot at a time
        # Every occupied row holds beta + its fingerprint; the rest of the leaf cube holds 1.
        ones_padding = E.sum(framework_selectors + table_selectors) + ONE
        totals.append(tree_values[side] + known + ones_padding)  # what the forms owe: the GKR value, less framework and padding

    return BusResult(tuple(claims), point, forms, (totals[0], totals[1], totals[2]))


# Table sumcheck -------------------------------------------------------------


def table_sumcheck(
    table_log_heights: Sequence[int],
    bus_forms: Sequence[Sequence[Form]],
    constraint_powers: Sequence[E],
    form_powers: Sequence[E],
    equality_point: MultilinearPoint,
    target: E,
    transcript: Transcript,
) -> list[ColumnClaim]:
    n_rounds = max(table_log_heights)
    challenges, claim = sumcheck(transcript, target, 4, [None] * n_rounds)
    point = list(reversed(challenges))
    weights = [ONE] * len(TABLES)
    for variable, challenge in enumerate(point):
        equality = ONE + equality_point[variable] + challenge
        for index, height in enumerate(table_log_heights):
            weights[index] *= equality if height > variable else challenge

    final = ZERO
    cursor = 0
    claims: list[ColumnClaim] = []
    for table, height, forms, weight in zip(TABLES, table_log_heights, bus_forms, weights, strict=True):
        evaluations = tuple(transcript.next_scalars(table.width))
        summand = dot(constraint_powers[cursor : cursor + table.n_constraints], table.constraints(evaluations))
        final += weight * (summand + dot(form_powers, [form.evaluate(evaluations.__getitem__) for form in forms]))
        cursor += table.n_constraints
        claims.extend(ColumnClaim(GLOBAL_COLUMN_BASES[table.opcode] + local, tuple(point[:height]), value) for local, value in enumerate(evaluations))
    require(final == claim, "table sumcheck terminal mismatch")
    return claims


R1CS_DIGEST = bytes.fromhex("537ad20790308f8eb8c0e8bd3e6c58ee64573371e3d53c30613dd04d87c0b7ea")

# The columns no instruction table owns. They come first in the global column numbering, the tables after.
NUM_GLOBAL_COLUMNS = 6
MEMORY_0, MEMORY_1, MEMORY_2, MEMORY_FINAL_COUNTERS, BYTECODE_FINAL_COUNTERS, QFLOCK = range(NUM_GLOBAL_COLUMNS)

BLAKE2S_R1CS_LOG_SIZE = 14
K_BITS = 64
FLOCK_K_SKIP = log2_ceil(K_BITS)
LOG_PACKING = log2_ceil(K_BITS)  # bits per committed K-element (pcs::pack::LOG_PACKING)

FLOCK_NUM_LINCHECK_ROUNDS = BLAKE2S_R1CS_LOG_SIZE - FLOCK_K_SKIP
QFLOCK_SLOT_BITS = BLAKE2S_R1CS_LOG_SIZE - LOG_PACKING
BLAKE2S_CONSTANT_COLUMN = 512


@dataclass(frozen=True)
class Layout:
    log_memory: int
    log_bytecode: int
    bytecode: Sequence[K]
    push: tuple[BusBlock, ...]
    pull: tuple[BusBlock, ...]
    count: tuple[BusBlock, ...]
    placements: tuple[Placement, ...]
    stack_log: int
    table_log_heights: tuple[int, ...]


def _cols(columns: Sequence[str], *names: str) -> tuple[int, ...]:
    assert set(names) <= set(columns), f"unknown columns: {sorted(set(names) - set(columns))}"
    return tuple(columns.index(name) for name in names)


def _gpow(index: int) -> E:
    return GEN**index


def _const(value: E | int) -> Form:
    return Form({(): value if isinstance(value, E) else E(value)})


def _col(index: int, exponent: int = 0) -> Form:
    return Form({(index,): _gpow(exponent)})


def _prod(a: int, b: int, exponent: int = 0) -> Form:
    return Form({tuple(sorted((a, b))): _gpow(exponent)})


SEP_STATE = ONE
SEP_MEM = GEN
SEP_BYTECODE = GEN**2


class Flushes:
    def __init__(self) -> None:
        self.push: list[tuple[Form, ...]] = []
        self.pull: list[tuple[Form, ...]] = []

    def pair(self, push: Sequence[Form], pull: Sequence[Form]) -> None:
        self.push.append(tuple(push))
        self.pull.append(tuple(pull))

    def state_derived(self, pc: int, fp: int, npc: Form, nfp: Form) -> None:
        self.pair((_const(SEP_STATE), npc, nfp), (_const(SEP_STATE), _col(pc), _col(fp)))

    def state_step(self, pc: int, fp: int) -> None:
        self.state_derived(pc, fp, _col(pc, 1), _col(fp))

    def _counted(self, prefix: Sequence[Form], count: int, suffix: Sequence[Form]) -> None:
        self.pair((*prefix, _col(count, 1), *suffix), (*prefix, _col(count), *suffix))

    def bytecode(self, pc: int, count: int, opcode: int, operands: Sequence[Form]) -> None:
        self._counted((_const(SEP_BYTECODE), _col(pc)), count, (_const(_gpow(opcode)), *operands))

    def memory(self, address: Form, count: int, values: Sequence[Form]) -> None:
        self._counted((_const(SEP_MEM), address), count, values)

    def memory_cols(self, address: Form, count: int, *columns: int) -> None:
        self.memory(address, count, [_col(column) for column in columns] + [_const(ZERO)] * (3 - len(columns)))


# The instruction tables ------------------------------------------------------


@dataclass(frozen=True)
class Table:
    """One instruction's table: its columns, its bus flushes, its constraints."""

    name: str
    opcode: int  # also its index in TABLES, so g^opcode is its bytecode tag
    columns: tuple[str, ...]
    flushes: Flushes
    constraints: Callable[[Sequence[E]], tuple[E, ...]] = lambda _: ()

    @property
    def n_constraints(self) -> int:
        return len(self.constraints([ZERO] * self.width))

    @property
    def width(self) -> int:
        return len(self.columns)

    @property
    def count_columns(self) -> tuple[int, ...]:
        return tuple(i for i, name in enumerate(self.columns) if name.startswith("cnt"))


def _flushes_arith(opcode: int, multiply: bool) -> Flushes:
    pc, fp, o_a, o_b, o_c, cnt_a, cnt_b, cnt_c, cnt_bc = _cols(ARITH_COLUMNS, "pc", "fp", "o_a", "o_b", "o_c", "cnt_a", "cnt_b", "cnt_c", "cnt_bc")
    va, vb = _cols(ARITH_COLUMNS, "va_0", "va_1", "va_2"), _cols(ARITH_COLUMNS, "vb_0", "vb_1", "vb_2")
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, opcode, (_col(o_a), _col(o_b), _col(o_c), _const(ZERO), _const(ZERO)))
    flushes.memory_cols(_prod(fp, o_a), cnt_a, *va)
    flushes.memory_cols(_prod(fp, o_b), cnt_b, *vb)
    TOWER_LANES = (((0, 0), (1, 2), (2, 1)), ((0, 1), (1, 0), (1, 2), (2, 1), (2, 2)), ((0, 2), (1, 1), (2, 0), (2, 2)))
    result = (
        tuple(Form.sum(_prod(va[j], vb[k]) for j, k in lane) for lane in TOWER_LANES)
        if multiply
        else tuple(_col(va[i]) + _col(vb[i]) for i in range(3))
    )
    flushes.memory(_prod(fp, o_c), cnt_c, result)
    return flushes


def _flushes_set() -> Flushes:
    pc, fp, o, cnt, cnt_bc = _cols(SET_COLUMNS, "pc", "fp", "o", "cnt", "cnt_bc")
    k = _cols(SET_COLUMNS, "k_0", "k_1", "k_2")
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, OP_SET, (_col(o), *(_col(limb) for limb in k), _const(ZERO)))
    flushes.memory_cols(_prod(fp, o), cnt, *k)
    return flushes


def _flushes_deref() -> Flushes:
    pc, fp, o1, o2, o3, f_pc, f_fp, ptr = _cols(DEREF_COLUMNS, "pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr")
    cnt_ptr, cnt_target, cnt_local, cnt_bc = _cols(DEREF_COLUMNS, "cnt_ptr", "cnt_target", "cnt_local", "cnt_bc")
    v3 = _cols(DEREF_COLUMNS, "v3_0", "v3_1", "v3_2")

    def gated(lane: int) -> list[Form]:
        return [_col(lane), _prod(f_pc, lane), _prod(f_fp, lane)]

    # v2 = (1 + f_pc + f_fp)*v3 + f_pc*(g^2*pc) + f_fp*fp, lane-wise: only the low lane takes the two K-valued sources.
    store = (Form.sum((*gated(v3[0]), _prod(f_pc, pc, 2), _prod(f_fp, fp))), Form.sum(gated(v3[1])), Form.sum(gated(v3[2])))
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, OP_DEREF, (_col(o1), _col(o2), _col(o3), _col(f_pc), _col(f_fp)))
    flushes.memory_cols(_prod(fp, o1), cnt_ptr, ptr)
    flushes.memory(_prod(ptr, o2), cnt_target, store)
    flushes.memory_cols(_prod(fp, o3), cnt_local, *v3)
    return flushes


def _flushes_jump() -> Flushes:
    pc, fp, o_c, o_d, o_f, cond, dest, frame, b = _cols(JUMP_COLUMNS, "pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "b")
    cnt_c, cnt_d, cnt_f, cnt_bc = _cols(JUMP_COLUMNS, "cnt_c", "cnt_d", "cnt_f", "cnt_bc")
    flushes = Flushes()
    # next_pc = b*dest + (b+1)*g*pc, next_fp = b*frame + (b+1)*fp, both derived.
    flushes.state_derived(pc, fp, _prod(b, dest) + _prod(b, pc, 1) + _col(pc, 1), _prod(b, frame) + _prod(b, fp) + _col(fp))
    flushes.bytecode(pc, cnt_bc, OP_JUMP, (_col(o_c), _col(o_d), _col(o_f), _const(ZERO), _const(ZERO)))
    flushes.memory_cols(_prod(fp, o_c), cnt_c, cond)
    flushes.memory_cols(_prod(fp, o_d), cnt_d, dest)
    flushes.memory_cols(_prod(fp, o_f), cnt_f, frame)
    return flushes


def _jump_constraints(columns: Sequence[E]) -> tuple[E, ...]:
    condition, inverse, flag = (columns[index] for index in _cols(JUMP_COLUMNS, "v_cond", "w", "b"))
    return (flag + condition * inverse, condition * (flag + ONE))


def _flushes_blake2s() -> Flushes:
    pc, fp, cnt_bc = _cols(BLAKE2S_COLUMNS, "pc", "fp", "cnt_bc")
    operands = _cols(BLAKE2S_COLUMNS, "o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md")
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, OP_BLAKE2S, tuple(_col(i) for i in operands))
    # The nine cells read, as (cell, operand, offset from it): four addressed message chunks, then
    # the consecutive chaining-value and output pairs, then the metadata cell (the byte counter and
    # the two flags). Each holds two q_flock limbs and a zero top.
    cells = (("m0", "o_0", 0), ("m1", "o_1", 0), ("m2", "o_2", 0), ("m3", "o_3", 0),
             ("cv0", "o_v", 0), ("cv1", "o_v", 1), ("out0", "o_out", 0), ("out1", "o_out", 1),
             ("md", "o_md", 0))  # fmt: skip
    for cell, operand, exponent in cells:
        address, count, lo, hi = _cols(BLAKE2S_COLUMNS, operand, f"cnt_{cell}", f"{cell}_lo", f"{cell}_hi")
        flushes.memory_cols(_prod(fp, address, exponent), count, lo, hi)
    return flushes


OP_XOR, OP_MUL, OP_SET, OP_DEREF, OP_JUMP, OP_BLAKE2S = range(6)

ARITH_COLUMNS = ("pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a", "cnt_b", "cnt_c", "cnt_bc",)  # fmt: skip
SET_COLUMNS = ("pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc")
DEREF_COLUMNS = ("pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2",  "cnt_ptr", "cnt_target", "cnt_local", "cnt_bc",)  # fmt: skip
JUMP_COLUMNS = ("pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc", "w", "b",)  # fmt: skip
BLAKE2S_COLUMNS = (
    "pc", "fp", "o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md",
    # These eighteen value limbs live in q_flock, not here: each is already a flock witness slot.
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi",
    "out0_lo", "out0_hi", "out1_lo", "out1_hi", "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "md_lo", "md_hi",
    # ...and the read counts, committed here like every other column.
    "cnt_m0", "cnt_m1", "cnt_m2", "cnt_m3", "cnt_cv0", "cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md", "cnt_bc",
)  # fmt: skip

TABLES = (
    Table("xor", OP_XOR, ARITH_COLUMNS, _flushes_arith(OP_XOR, multiply=False)),
    Table("mul", OP_MUL, ARITH_COLUMNS, _flushes_arith(OP_MUL, multiply=True)),
    Table("set", OP_SET, SET_COLUMNS, _flushes_set()),
    Table("deref", OP_DEREF, DEREF_COLUMNS, _flushes_deref()),
    Table("jump", OP_JUMP, JUMP_COLUMNS, _flushes_jump(), _jump_constraints),
    Table("blake2s", OP_BLAKE2S, BLAKE2S_COLUMNS, _flushes_blake2s()),
)

# Where in the flock witness each embedded BLAKE2s limb live: one 64-bit slot per limb, the chaining value first, then the
# digest, the message block and the metadata. Slots 8 and 9 are flock's constant wire and the padding up to its message base, which no memory cell carries.
BLAKE2S_SLOTS = (
    "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "out0_lo", "out0_hi", "out1_lo", "out1_hi", None, None,
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi", "md_lo", "md_hi",
)  # fmt: skip

TABLE_WIDTHS = tuple(t.width for t in TABLES)
GLOBAL_COLUMN_BASES = tuple(NUM_GLOBAL_COLUMNS + sum(TABLE_WIDTHS[:table]) for table in range(len(TABLES)))


def build_layout(bytecode: Sequence[K], log_memory: int, table_log_heights: Sequence[int]) -> Layout:
    log_bytecode = log2_strict(len(bytecode)) - BUS_BITS
    require(
        16 <= log_memory <= 32
        and all(0 <= log_height <= 32 for log_height in table_log_heights)
        and table_log_heights[OP_BLAKE2S] >= 3
        and 0 <= log_bytecode <= 32,
        "invalid announced table sizes",
    )

    push: list[BusBlock] = []
    pull: list[BusBlock] = []
    count: list[BusBlock] = []
    for table, height in zip(TABLES, table_log_heights, strict=True):
        flushes = table.flushes
        for coordinates in flushes.push:
            push.append(BusBlock(height, coordinates, table.opcode))
        for coordinates in flushes.pull:
            pull.append(BusBlock(height, coordinates, table.opcode))
        for local in table.count_columns:
            count.append(BusBlock(height, (_col(local),), table.opcode))

    # Every column's log size, in global order: the framework's, q_flock's, then each table's block.
    qflock_kappa = table_log_heights[OP_BLAKE2S] + QFLOCK_SLOT_BITS
    kappas = [log_memory, log_memory, log_memory, log_memory, log_bytecode, qflock_kappa]
    for table in TABLES:
        kappas += [table_log_heights[table.opcode]] * table.width

    # A BLAKE2s value limb gets no block of its own: it is committed inside q_flock, whose slots
    # interleave, so it sits at q_flock's offset behind its own slot's bits. Same width either way.
    limbs = {GLOBAL_COLUMN_BASES[OP_BLAKE2S] + _cols(BLAKE2S_COLUMNS, name)[0]: slot for slot, name in enumerate(BLAKE2S_SLOTS) if name}
    blocks = {column: kappa for column, kappa in enumerate(kappas) if column not in limbs}
    block_offsets, total_log = stack_offsets(list(blocks.values()))
    offsets = dict(zip(blocks, block_offsets))
    stack_log = max(MIN_STACKED_LOG, total_log)  # Floor at the PCS minimum
    placements = [
        Placement(kappa, offsets[QFLOCK] + limbs[column], QFLOCK_SLOT_BITS) if column in limbs else Placement(kappa, offsets[column])
        for column, kappa in enumerate(kappas)
    ]
    return Layout(log_memory, log_bytecode, bytecode, tuple(push), tuple(pull), tuple(count), tuple(placements), stack_log, tuple(table_log_heights))


# WHIR opening ----------------------------------------------------------------

INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 4
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3
RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1
RESIDUAL_MAX_LOG = 5
QUERY_GRINDING_BITS = 17

MIN_STACKED_LOG = 15
MAX_STACKED_LOG = 28

WHIR_QUERIES = (((223,55), (223,56,30), (223,56,31), (224,56,32), (224,56,32), (224,56,32,22), (224,56,32,22), (225,56,32,23), (225,56,32,23), (225,56,32,23,17), (226,56,32,23,17), (226,56,32,23,18), (227,56,32,23,18), (228,56,32,23,18,14)), ((112,45), (112,45,27), (112,45,28), (112,45,28), (112,45,28), (112,45,28,20), (112,45,28,20), (112,45,28,21), (112,45,28,21), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,17,13)), ((75,37), (75,37,24), (75,38,25), (75,38,25), (75,38,25), (75,38,25,18), (75,38,25,19), (75,38,25,19), (75,38,25,19), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (76,38,25,19,16,13)), ((56,32), (56,32,22), (56,32,22), (56,32,23), (56,32,23), (56,32,23,17), (56,32,23,17), (56,32,23,18), (56,32,23,18), (57,32,23,18,14), (57,32,23,18,14), (57,32,23,18,15), (57,33,23,18,15), (57,33,23,18,15,12)))  # fmt: skip


@dataclass(frozen=True)
class WhirConfig:
    log_inv_rates: tuple[int, ...]
    folds: tuple[int, ...]
    queries: tuple[int, ...]


def derive_config(log_n: int, log_inv_rate: int) -> WhirConfig:
    """The opening shape at this size and rate: the ladder geometry, then the
    tabulated query counts."""
    require(MIN_STACKED_LOG <= log_n <= MAX_STACKED_LOG and 1 <= log_inv_rate <= 4, "invalid WHIR shape")
    folds = [INITIAL_FOLDING_FACTOR]
    log_inv_rates = [log_inv_rate]
    remaining = log_n - INITIAL_FOLDING_FACTOR
    while remaining > RESIDUAL_MAX_LOG:
        first = len(folds) == 1
        log_inv_rates.append(log_inv_rates[-1] + folds[-1] - (RS_DOMAIN_INITIAL_REDUCTION_FACTOR if first else RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR))
        fold = min(SUBSEQUENT_FOLDING_FACTOR, remaining)
        remaining -= fold
        folds.append(fold)
    queries = WHIR_QUERIES[log_inv_rate - 1][log_n - MIN_STACKED_LOG]
    require(len(queries) == len(folds), "tabulated query count does not match the ladder")
    return WhirConfig(log_inv_rates=tuple(log_inv_rates), folds=tuple(folds), queries=queries)


def _ext_row(words: Sequence[K]) -> tuple[E, ...]:
    """Regroup a level's leaf words into the E values they encode, three per lane."""
    return tuple(E(*words[i : i + 3]) for i in range(0, len(words), 3))


def sample_queries(transcript: Transcript, block_length: int, count: int) -> list[int]:
    depth = log2_strict(block_length)
    per_word = 192 // depth
    result: list[int] = []
    while len(result) < count:
        bits = int(transcript.sample())
        for chunk in range(min(per_word, count - len(result))):
            result.append((bits >> (chunk * depth)) & (block_length - 1))
    return result


def _enforced_sum(rows: Sequence[Sequence[K | E]], folds: Sequence[E], query_weights: Sequence[E]) -> E:
    lane_weights = eq_kernel(folds)
    total = ZERO
    for query_weight, row in zip(query_weights, rows, strict=True):
        total += query_weight * dot(row, lane_weights)
    return total


def _subspace_roots(log_n: int) -> list[E]:
    roots = [ONE]
    layer = [E(2**i) for i in range(1, log_n + 1)]
    for _ in range(log_n):
        layer = [value**2 + roots[-1] * value for value in layer]
        roots.append(layer.pop(0))
    return roots


def _induced_weight(message_log: int, queries: Sequence[int], query_weights: Sequence[E], point: Sequence[E]) -> E:
    """The level's batched query claims, as one weight at `point`.

    Each query contributes the novel-basis column weight of doc annex B, Lemma
    lem:colweight, `prod_k (1 + p_k (1 + W-hat_k(x_q)))`, scaled by its power of
    the level's batching challenge.
    """
    require(len(point) == message_log, "bad induced-basis dimensions")
    roots = _subspace_roots(message_log)
    inverses = [value.inv() if value else ZERO for value in roots]
    total = ZERO
    for weight, query in zip(query_weights, queries, strict=True):
        basis = E(query)
        product = weight
        for coordinate, challenge in enumerate(point):
            product *= ONE + challenge * (ONE + basis * inverses[coordinate])
            basis = basis**2 + roots[coordinate] * basis
        total += product
    return total


@dataclass(frozen=True)
class GluedClaim:
    """One claim folded into the running sumcheck, and the weight it owes back.

    A level's batched queries and an out-of-domain claim differ only in that
    weight: both are a power of the level's lambda times a function of the
    terminal point, restricted to the level's own message coordinates.
    """

    scalar: E  # the power of lambda it was glued with
    fold_start: int  # how many fold challenges preceded the level
    weight_at: Callable[[Sequence[E]], E]


def verify_whir(transcript: Transcript, log_n: int, log_inv_rate: int, target: E, root: Digest, evaluate_basis: Callable[[Sequence[E]], E]) -> None:
    """Verify the base-field multilevel opening with a one-point terminal check."""
    config = derive_config(log_n, log_inv_rate)
    levels = len(config.folds)

    running_target = target
    running_quad = transcript.sumcheck_round_poly(3, target)
    folds: list[E] = []
    glued: list[GluedClaim] = []
    current_root = root

    for level, (fold_count, level_rate) in enumerate(zip(config.folds, config.log_inv_rates, strict=True)):
        level_folds: list[E] = []
        for _ in range(fold_count):
            challenge = transcript.sample()
            folds.append(challenge)
            level_folds.append(challenge)
            running_target = poly_eval(running_quad, challenge)
            running_quad = transcript.sumcheck_round_poly(3, running_target)

        message_log = log_n - len(folds)
        final_level = level == levels - 1
        # The level's claims, held until its batching challenge is drawn: the
        # OOD claims first, then the query batch (Annex B, Protocol 1 step 1).
        pending: list[tuple[E, Sequence[E], Callable[[Sequence[E]], E]]] = []
        if final_level:
            residual = tuple(transcript.next_scalars(2**message_log))
        else:
            next_root = Digest.from_halves(*transcript.next_scalars(2))
            ood_point = tuple(transcript.samples(message_log))
            ood_value = transcript.next_scalar()
            pending.append((ood_value, transcript.sumcheck_round_poly(3, ood_value), lambda x, z=ood_point: eq_eval(z, x)))

        transcript.grind_check(QUERY_GRINDING_BITS)
        block_length = 2 ** (message_log + level_rate)
        queries = sample_queries(transcript, block_length, config.queries[level])
        # One batching challenge per level, drawn once every claim it batches is
        # fixed: the OOD claims above and these query positions.
        lam = transcript.sample()
        query_weights = powers(lam, len(queries))
        # Level 0 committed the K witness, one leaf word per lane; every deeper
        # level a folded E one, three words per lane.
        lanes = 2**fold_count
        words = transcript.merkle(current_root, block_length, queries, lanes if level == 0 else 3 * lanes)
        rows: list[Sequence[K | E]] = [tuple(reversed(row)) for row in words] if level == 0 else [_ext_row(row) for row in words]
        enforced = _enforced_sum(rows, level_folds, query_weights)

        # Every commitment, including the last one, enters through an intro
        # message; the level's claims are then batched with powers of `lam`,
        # the running claim keeping lam^0 = 1.
        batch = (message_log, tuple(queries), tuple(query_weights))
        pending.append((enforced, transcript.sumcheck_round_poly(3, enforced), lambda x, b=batch: _induced_weight(*b, x)))
        scalar = ONE
        for value, intro, weight_at in pending:
            scalar *= lam
            running_quad = [q + scalar * i for q, i in zip(running_quad, intro, strict=True)]
            running_target += scalar * value
            glued.append(GluedClaim(scalar, len(folds), weight_at))

        if final_level:
            # Finish the remaining sumcheck rounds and close on one evaluation
            # of every basis at the resulting point.
            tail_folds: list[E] = []
            for round_index in range(message_log):
                challenge = transcript.sample()
                running_target = poly_eval(running_quad, challenge)
                tail_folds.append(challenge)
                if round_index + 1 < message_log:
                    running_quad = transcript.sumcheck_round_poly(3, running_target)
            # Each glued claim is rebound at the terminal point: the fold
            # challenges its level fixed after it was made, then the tail.
            point = list(folds) + tail_folds
            lane_folds = config.folds[0]
            weight = evaluate_basis(point[lane_folds:] + point[:lane_folds])
            for claim in glued:
                weight += claim.scalar * claim.weight_at(list(folds[claim.fold_start :]) + tail_folds)
            terminal = weight * multilinear_eval(residual, tail_folds)
            require(terminal == running_target, "WHIR terminal check failed")
            return
        current_root = next_root

    raise VerificationError("WHIR verification ended without a terminal level")


# Flock reduction -------------------------------------------------------------

PHI_BASIS = (E(0x0000000000000001), E(0x033CE8BEDDC8A656), E(0x512620375ED2A108), E(0x0C9E636090AAFC01), E(0xBA4F3CD82801769C), E(0xBA26E7904ADB4A47), E(0x467698598926DC01), E(0x4418AE808B28BDD0))  # fmt: skip
PHI = tuple(E.sum(PHI_BASIS[bit] for bit in range(8) if value >> bit & 1) for value in range(256))


@cache
def _window_denominator(count: int) -> E:
    """The one barycentric denominator `PHI[:count]` has: `prod_(k != 0) PHI[k]`, inverted.

    PHI is F2-linear in its index, so `PHI[i] + PHI[j] = PHI[i ^ j]`, and over a power-of-two prefix
    `j -> i ^ j` only permutes the block. Every node is left the same product.
    """
    return reduce(mul, PHI[1:count], ONE).inv()


def lagrange_weights(count: int, point: E) -> list[E]:
    """The barycentric weights of `PHI[:count]` at `point`, by prefix and suffix numerator products."""
    differences = [point + node for node in PHI[:count]]
    prefix = list(accumulate(differences, mul, initial=ONE))
    suffix = list(accumulate(reversed(differences), mul, initial=ONE))[::-1]
    denominator = _window_denominator(count)
    return [p * s * denominator for p, s in zip(prefix[:count], suffix[1:])]


def lagrange_interpolate(count: int, values: Sequence[E], point: E) -> E:
    return dot(lagrange_weights(count, point), values)


@dataclass(frozen=True)
class ZerocheckResult:
    z_skip: E
    chi: MultilinearPoint
    v_a: E
    v_b: E
    v_c: E


def verify_flock_zerocheck(log_n: int, transcript: Transcript) -> ZerocheckResult:
    """The zerocheck: one univariate skip round, then nflock quadratic ones.
    C rides those rounds with AB, so all three claims come out at one point."""
    # The point r, every coordinate sampled.
    r = transcript.samples(log_n - FLOCK_K_SKIP)

    # P = P^AB + P^C on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    p_coset = transcript.next_scalars(K_BITS)
    z_skip = transcript.sample()
    v_p = lagrange_interpolate(2 * K_BITS, [ZERO] * K_BITS + list(p_coset), z_skip)

    # nflock quadratic rounds on P, closed by v_a, v_b.
    chi, running = sumcheck(transcript, v_p, 3, r)
    v_a, v_b = transcript.next_scalars(2)
    v_c = running + v_a * v_b
    return ZerocheckResult(z_skip, chi, v_a, v_b, v_c)


def verify_flock_lincheck(zc: ZerocheckResult, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """Lincheck at the quirky point (z_skip, chi): the claim's point, then its 64 slices s."""
    alpha = transcript.sample()  # batches the two matrix identities, the c claim and the constant-position claim
    # e_row: phi8 Lagrange in the skip coordinate, eq in the slot variables.
    skip_weights = lagrange_weights(K_BITS, zc.z_skip)
    chi_in = zc.chi[:FLOCK_NUM_LINCHECK_ROUNDS]
    e_row = [weight * value for weight in eq_kernel(chi_in) for value in skip_weights]

    # The 8 rounds that bind the high column coordinates, leaving 64 unfolded.
    claim = zc.v_a + alpha * zc.v_b + alpha**2 * zc.v_c + alpha**3
    round_challenges, r_lc = sumcheck(transcript, claim, 3, [None] * FLOCK_NUM_LINCHECK_ROUNDS)

    # The residual, then the terminal identity: pin term and c term included.
    # C = I, so the c weight is e_row itself, and both sides being tensors it
    # collapses to eq(chi_in, chi_in_prime) times a 64-term Lagrange combination.
    s = tuple(transcript.next_scalars(K_BITS))
    chi_in_prime = tuple(reversed(round_challenges))
    w_col = [value * weight for weight in eq_kernel(chi_in_prime) for value in s]
    terminal = (
        blake2s_bilinear(alpha, e_row, w_col)
        + alpha**2 * eq_eval(chi_in, chi_in_prime) * dot(skip_weights, s)
        + alpha**3 * w_col[BLAKE2S_CONSTANT_COLUMN]
    )
    require(terminal == r_lc, "Flock lincheck terminal mismatch")
    return chi_in_prime + zc.chi[FLOCK_NUM_LINCHECK_ROUNDS:], s


def blake2s_row_values(column_weights: Sequence[E]) -> tuple[list[E], list[E]]:
    """Compute `A0 w` and `B0 w` by one forward walk of the circuit."""
    size = 2**BLAKE2S_R1CS_LOG_SIZE
    constant = BLAKE2S_CONSTANT_COLUMN
    message_base = 640
    counter_low = 1152
    counter_high = 1184
    final_flag = 1216
    last_node_flag = 1248
    gates_base = 1280
    gate_stride = 184
    left_values = [ZERO] * size
    right_values = [ZERO] * size

    def slots(base: int) -> tuple[E, ...]:
        return tuple(column_weights[base + bit] for bit in range(32))

    empty_word = (ZERO,) * 32

    def literal(value: int) -> tuple[E, ...]:
        return tuple(column_weights[constant] if value >> bit & 1 else ZERO for bit in range(32))

    def xor(x: Sequence[E], y: Sequence[E]) -> tuple[E, ...]:
        return tuple(a + b for a, b in zip(x, y, strict=True))

    def rotate_right(word: Sequence[E], amount: int) -> tuple[E, ...]:
        return tuple(word[(bit + amount) & 31] for bit in range(32))

    def add(x: Sequence[E], y: Sequence[E], carry_base: int) -> tuple[E, ...]:
        carry = ZERO
        output = []
        for bit in range(32):
            if bit < 31:
                left_values[carry_base + bit] = x[bit] + carry
                right_values[carry_base + bit] = y[bit] + carry
            output.append(x[bit] + y[bit] + carry)
            if bit < 31:
                carry += column_weights[carry_base + bit]
        return tuple(output)

    def add3(x: Sequence[E], y: Sequence[E], z: Sequence[E], base: int) -> tuple[E, ...]:
        """Fused three-operand add: 31 majority rows then 30 ripple rows.

        The majority of bit `i` is `maj_aux[i] + z[i]`, since over GF(2)
        `(x+z)(y+z) = xy + xz + yz + z`; then `x + y + z` is the ripple sum of
        `p = x^y^z` against `q[i] = maj[i-1]`, whose bit 0 is zero, so the
        ripple layer's bit 0 needs no row and slot `base + 31 + i - 1` carries
        bit `i`.
        """
        majority = []
        for bit in range(31):
            left_values[base + bit] = x[bit] + z[bit]
            right_values[base + bit] = y[bit] + z[bit]
            majority.append(column_weights[base + bit] + z[bit])
        ripple_base = base + 31
        carry = ZERO
        output = []
        for bit in range(32):
            q = ZERO if bit == 0 else majority[bit - 1]
            left = x[bit] + y[bit] + z[bit] + carry
            output.append(left + q)
            if 1 <= bit <= 30:
                left_values[ripple_base + bit - 1] = left
                right_values[ripple_base + bit - 1] = q + carry
                carry += column_weights[ripple_base + bit - 1]
        return tuple(output)

    def linear_rows(values: Sequence[E], base: int) -> None:
        for bit in range(32):
            left_values[base + bit] = values[bit]
            right_values[base + bit] = column_weights[constant]

    for base, length in ((0, 256), (message_base, 512), (counter_low, 128)):
        for row in range(base, base + length):
            left_values[row] = column_weights[row]
            right_values[row] = column_weights[constant]

    # v[0..8] = h, v[8..12] = IV[0..4], v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1).
    state = [empty_word for _ in range(16)]
    for word in range(8):
        state[word] = slots(32 * word)
    for word in range(4):
        state[8 + word] = literal(BLAKE2S_IV[word])
    for word, base in enumerate((counter_low, counter_high, final_flag, last_node_flag)):
        state[12 + word] = xor(literal(BLAKE2S_IV[4 + word]), slots(base))

    for round_index in range(10):
        sigma = BLAKE2S_SIGMA[round_index]
        for gate_index, (lane_a, lane_b, lane_c, lane_d) in enumerate(BLAKE2S_G_LANES):
            gate = round_index * 8 + gate_index
            gate_base = gates_base + gate_stride * gate
            a, b, c, d = state[lane_a], state[lane_b], state[lane_c], state[lane_d]
            mx = slots(message_base + 32 * sigma[2 * gate_index])
            my = slots(message_base + 32 * sigma[2 * gate_index + 1])
            a1 = add3(a, b, mx, gate_base)
            d1 = rotate_right(xor(d, a1), 16)
            c1 = add(c, d1, gate_base + 61)
            b1 = rotate_right(xor(b, c1), 12)
            a2 = add3(a1, b1, my, gate_base + 92)
            d2 = rotate_right(xor(d1, a2), 8)
            c2 = add(c1, d2, gate_base + 153)
            b2 = rotate_right(xor(b1, c2), 7)
            # Every lane cascades: this encoding materializes no intermediate word.
            state[lane_a] = a2
            state[lane_b] = b2
            state[lane_c] = c2
            state[lane_d] = d2

    # out[w] = h[w] ^ v[w] ^ v[w+8], the only materialized words.
    for word in range(8):
        out = xor(xor(state[word], state[word + 8]), slots(32 * word))
        linear_rows(out, 256 + 32 * word)

    left_values[constant] = column_weights[constant]
    right_values[constant] = column_weights[constant]
    return left_values, right_values


def blake2s_bilinear(alpha: E, row_weights: Sequence[E], column_weights: Sequence[E]) -> E:
    """Compute `e_row^T (A0 + alpha B0) w_col` from the two forward row vectors."""
    left_values, right_values = blake2s_row_values(column_weights)
    return dot(row_weights, left_values) + alpha * dot(row_weights, right_values)


def verify_flock(log_n: int, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """The reduction in protocol order: zerocheck, then lincheck. What it leaves is the
    point and the 64 claims s[i] = z(i, point), i < 64, for ring switching to bind."""
    zc = verify_flock_zerocheck(log_n, transcript)
    return verify_flock_lincheck(zc, transcript)


# Ring switching --------------------------------------------------------------

# The Frobenius shifts of the six stages composing Phi, one challenge each.
RING_MAP_SHIFTS = (32, 16, 8, 4, 2, 1)


def _phi(value: E, challenges: Sequence[E]) -> E:
    """The drawn map, stage by stage: `a_p+1 = a_p + f_p a_p^(2^shift)`."""
    for challenge, shift in zip(challenges, RING_MAP_SHIFTS, strict=True):
        value += challenge * value ** (2**shift)
    return value


def _ring_weight(r: MultilinearPoint, r_prime: Sequence[E], coefficients: Sequence[E]) -> E:
    """The weight `W(u) = Phi(eq(r, u))`, extended and evaluated by the opening at
    `r_prime`: `sum_k c_k prod_n (1 + r_n^(2^k) + r'_n)`."""
    total = ZERO
    frobenius = list(r)
    for c in coefficients:
        product = c
        for value, challenge in zip(frobenius, r_prime, strict=True):
            product *= ONE + value + challenge
        total += product
        frobenius = [value**2 for value in frobenius]
    return total


def ring_switch(point: MultilinearPoint, s: Sequence[E], transcript: Transcript) -> tuple[E, Callable[[Sequence[E]], E]]:
    """The 64 claims s[i] = z(i, point) become the one dense claim `sum_u W(u) qflock(u) = target`.

    Draw Phi once they are fixed, then take the target `T = sum_i x^i Phi(s_i)` against the
    MLE-friendly weight `W(u) = Phi(eq(point, u))`. Returns the target and W as a closure."""
    challenges = transcript.samples(len(RING_MAP_SHIFTS))
    # The same map as a Frobenius sum, `Phi(a) = sum_k c_k a^(2^k)` for k < 64.
    coefficients = [reduce(mul, (f ** (2 ** (k % s)) for f, s in zip(challenges, RING_MAP_SHIFTS) if k & s), ONE) for k in range(K_BITS)]
    target = poly_eval([_phi(value, challenges) for value in s], GEN)
    return target, lambda r_prime: _ring_weight(point, r_prime, coefficients)


# Stacked opening -------------------------------------------------------------


type StackClaim = tuple[Callable[[Sequence[E]], E], E]  # the weight it puts on the stack, and the value it claims for it


def verify_stacked_opening(transcript: Transcript, root: Digest, stack_log: int, log_inv_rate: int, claims: Sequence[StackClaim]) -> None:
    """Discharge every claim on the committed stack in one opening: the same powers of one challenge
    batch the values into the target, and the weights into the basis WHIR evaluates at its terminal point.
    """
    weights, values = zip(*claims, strict=True)
    scales = powers(transcript.sample(), len(claims))
    verify_whir(transcript, stack_log, log_inv_rate, dot(scales, values), root, lambda point: dot(scales, [weight(point) for weight in weights]))


def verify_execution(bytecode: Sequence[K], public_input: Digest, proof: Proof) -> None:
    bytecode_hash = blake2s_hash(b"".join(word.to_bytes() for word in bytecode))
    iv_preimage = b"leanvm" + pack("<Q", len(R1CS_DIGEST)) + R1CS_DIGEST + bytecode_hash.value
    fiat_shamir_IV = blake2s_hash(iv_preimage)
    transcript = Transcript(proof, fiat_shamir_IV, public_input)

    # 1] memory log-size, table log-size, and log-inv-rate in WHIR
    announced = transcript.next_scalars(2 + len(TABLES))
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced size has a nonzero high limb")
    log_memory = int(announced[0].c0)
    table_logs = tuple(int(value.c0) for value in announced[1 : 1 + len(TABLES)])
    log_inverse_rate = int(announced[-1].c0)
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    layout = build_layout(bytecode, log_memory, table_logs)
    require(MIN_STACKED_LOG <= layout.stack_log <= MAX_STACKED_LOG, "committed size outside the PCS window")

    # 2] parse WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    root = Digest.from_halves(*transcript.next_scalars(2))

    # 3] Bus: one batched GKR over the push, pull and count trees, then the leaf decomposition, which leaves each table a degree-2 claim.
    bus = verify_bus_balance(layout, transcript)

    # 4] One batched (back-loaded) "table sumcheck" over all six tables, at the bus point, proving the target the three
    # leaf claims derive and that constraints vanish. Every table takes a disjoint range of xi powers for its constraints
    xi = transcript.sample()
    n_constraints = sum(table.n_constraints for table in TABLES)
    xi_powers = powers(xi, n_constraints + 3)  # one power per constraint, then one per bus side, shared by every table
    constraint_powers, form_powers = xi_powers[:n_constraints], xi_powers[n_constraints:]
    target = dot(form_powers, bus.totals)
    table_sumcheck_claims = table_sumcheck(layout.table_log_heights, bus.forms, constraint_powers, form_powers, bus.point, target, transcript)
    claims = [*bus.claims, *table_sumcheck_claims]

    # 5] binding the public input
    public_challenge = transcript.sample()
    public_limbs = (*transcript.next_scalars(2), ZERO)
    require(poly_eval(public_limbs, Y) == multilinear_eval(public_input.halves(), [public_challenge]), "public input check failed")
    public_point = (public_challenge, *[ZERO] * (layout.placements[MEMORY_0].variables - 1))
    claims.extend(ColumnClaim(column, public_point, value) for column, value in zip((MEMORY_0, MEMORY_1, MEMORY_2), public_limbs))

    # 6] BLAKE2s validity via Flock
    flock_point, flock_s = verify_flock(BLAKE2S_R1CS_LOG_SIZE + layout.table_log_heights[OP_BLAKE2S], transcript)

    # 7] Ring-switching
    ringswitch_target, ringswitch_weight = ring_switch(flock_point, flock_s, transcript)
    # That claim is supported on q_flock's region of the stack, so its weight carries the
    # placement's selector, and it leads the batch, taking the first power.
    qflock = layout.placements[QFLOCK]
    ringswitch = (lambda x: qflock.eq_above(x) * ringswitch_weight(x[: qflock.variables]), ringswitch_target)
    verify_stacked_opening(transcript, root, layout.stack_log, log_inverse_rate, [ringswitch, *(c.on_stack(layout) for c in claims)])
    transcript.finish()


def main(argv: Sequence[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Verify a leanVM execution proof")
    parser.add_argument("bytecode", type=Path, help="stacked bytecode multilinear, little-endian 64-bit words")
    parser.add_argument("public_input", type=Path, help="256-bit public input")
    parser.add_argument("stream", type=Path, help="the proof's scalar stream, 24-byte little-endian field elements")
    parser.add_argument("merkle_openings", type=Path, help="every Merkle opening: its leaf's words, then its sibling digests")
    arguments = parser.parse_args(argv)
    try:
        encoded_bytecode = arguments.bytecode.read_bytes()
        require(len(encoded_bytecode) % 8 == 0, "bytecode is not a whole number of 64-bit words")
        bytecode = [K(int.from_bytes(encoded_bytecode[i : i + 8], "little")) for i in range(0, len(encoded_bytecode), 8)]
        proof = Proof.load(arguments.stream, arguments.merkle_openings)
        verify_execution(bytecode, Digest(arguments.public_input.read_bytes()), proof)
    except (OSError, ValueError, KeyError, VerificationError) as exc:
        parser.exit(1, f"verification failed: {exc}\n")
    print("verification succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
