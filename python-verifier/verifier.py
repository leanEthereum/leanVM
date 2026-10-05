from __future__ import annotations

import hashlib
import sys
from collections.abc import Callable, Container, Iterable, Sequence
from dataclasses import dataclass, field
from functools import cache, cached_property, reduce
from itertools import accumulate, count, islice, pairwise, product, repeat
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
    return _reduce(product)


def _base_square(value: int) -> int:
    """Squaring is additive in characteristic 2: bit i of the value lands on bit 2i of the product."""
    return _reduce(int("0".join(f"{value:b}"), 2))


def _reduce(product: int) -> int:
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
        if isinstance(other, K):
            return E(self.c0 * other, self.c1 * other, self.c2 * other)  # K sits in E as the constant limb
        rhs = self.lift(other)
        # y^3 = y + 1 folds the degree-4 product back into three limbs.
        p0 = self.c0 * rhs.c0
        p1 = self.c0 * rhs.c1 + self.c1 * rhs.c0
        p2 = self.c0 * rhs.c2 + self.c1 * rhs.c1 + self.c2 * rhs.c0
        p3 = self.c1 * rhs.c2 + self.c2 * rhs.c1
        p4 = self.c2 * rhs.c2
        return E(p0 + p3, p1 + p3 + p4, p2 + p4)

    __rmul__ = __mul__

    def square(self) -> E:
        """The product's cross terms cancel in characteristic 2, leaving c0^2 + c1^2 y^2 + c2^2 y^4, folded by y^3 = y + 1."""
        c0, c1, c2 = (K(_base_square(limb.value)) for limb in (self.c0, self.c1, self.c2))
        return E(c0, c2, c1 + c2)

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


def powers(base: E, count: int) -> list[E]:
    """`[1, base, base^2, ...]`, `count` terms."""
    return list(islice(accumulate(repeat(base), mul, initial=ONE), count))


# BLAKE2s and digests ---------------------------------------------------------

# The compression function's constants, which the hash circuit encodes (RFC 7693).
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

    @classmethod
    def from_halves(cls, low: E, high: E) -> Digest:
        """A digest as it travels on the stream: two 128-bit halves."""
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


def int_index_mle(base: int, shift: int, point: MultilinearPoint) -> E:
    """MLE of ``[base ^ (z << shift)]``, each integer read as the field element with those bits: linear in the point.
    With `base` a multiple of the region's size the XOR is the sum, so this is the column of addresses `base + (z << shift)`."""
    return E(base) + E.sum(challenge * E(1 << (bit + shift)) for bit, challenge in enumerate(point))


def sparse_mle(stretches: Sequence[tuple[int, Sequence[int]]], point: MultilinearPoint) -> E:
    """MLE of the column that holds each `(offset, words)` stretch and zero elsewhere, in time proportional to the
    stretches. A stretch is cut into aligned blocks, a power of two of words at a multiple of it, and such a block's
    share is its own extension in the low variables times the indicator of its offset's bits in the high ones."""
    total = ZERO
    for offset, words in stretches:
        while words:
            size = 1 << (len(words).bit_length() - 1)
            if offset:
                size = min(size, offset & -offset)
            low = size.bit_length() - 1
            selector = reduce(mul, (z if offset >> (low + j) & 1 else z + ONE for j, z in enumerate(point[low:])), ONE)
            total += selector * multilinear_eval([K(word) for word in words[:size]], point[:low])
            offset, words = offset + size, words[size:]
    return total


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
    return offsets, total


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
    def __init__(self, proof: Proof, fiat_shamir_IV: Digest, public_input: Sequence[K]) -> None:
        self.proof = proof
        self.state = compress(fiat_shamir_IV.words(), public_input)
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

    def merkle(self, root: Digest, block_length: int, queries: Sequence[int], leaf_words: int, zero_prefix: int = 0) -> list[tuple[K, ...]]:
        """Each query's leaf words, checked against `root`; the first `zero_prefix` words of every leaf must be zero."""
        height = log2_strict(block_length)
        rows = []
        for query in queries:
            leaf = self._merkle_data(8 * leaf_words)
            require(not any(leaf[: 8 * zero_prefix]), "a leaf's absent lanes are not zero")
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


def verify_gkr_grand_products(depth: int, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, E]]:
    shared = transcript.next_scalar()
    combiner = transcript.sample()
    point: list[E] = []
    values = (shared, shared)  # 2 grand product GKR are batched together, push and pull, under one root

    layer = depth
    while layer > 0:
        # Two levels a step. An odd depth starts with one.
        step = 1 if layer % 2 else 2
        claim = poly_eval(values, combiner)
        # The product is degree 2^step, so one more coefficient than that per round.
        x, claim = sumcheck(transcript, claim, 2**step + 1, point)

        children = [transcript.next_scalars(2**step) for _ in range(2)]
        products = [reduce(mul, child) for child in children]
        require(claim == poly_eval(products, combiner), f"GKR layer {layer}: children do not match the sumcheck")

        y = transcript.samples(step)
        values = [multilinear_eval(child, y) for child in children]
        combiner = transcript.sample()
        point = [*y, *x]
        layer -= step

    return tuple(point), (values[0], values[1])


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

    def on(self, columns: Container[int]) -> Form:
        """Its part linear in `columns`."""
        return Form({monomial: c for monomial, c in self.terms.items() if len(monomial) == 1 and monomial[0] in columns})


@dataclass(frozen=True)
class BusBlock:
    """One block of a bus side, always owned by a table. The four blocks no table owns are the framework, on `BusLayout`."""

    log_rows: int  # the owner's height: this block flushes 2^log_rows rows
    coordinates: tuple[Form, ...]  # the tuple flushed, over the owner's OWN local column indices; stays symbolic until its table sumcheck
    owner: int  # whose block it is, by opcode


@dataclass(frozen=True)
class Producer:
    """A lookup array's table side: entry x is pushed m_x times, m_x being its word in the multiplicity column read as an
    integer. Bit i of it is a push block of its own, whose row x is the entry's leaf raised to 2^i where that bit is set
    and 1 where it is not. The bus reads the low `bits` bits, enough for every read the tables can make of the array."""

    log_rows: int
    column: int  # the committed multiplicity column
    bits: int


@dataclass(frozen=True)
class BusLayout:
    """Where a side's blocks sit in the stacked leaf cube. Split by kind because framework coordinates are
    public, so the verifier evaluates their fingerprints outright, while a table's stay symbolic until its columns settle them,
    and a producer's bits become weights on its own sumcheck."""

    depth: int  # log2 of the padded cube, so how many layers the side's GKR walks
    framework: tuple[Placement, ...]  # the blocks no table owns, stacked first, in FRAMEWORK order
    tables: tuple[Placement, ...]  # one per block a table owns, in the side's own block order
    producers: tuple[tuple[Placement, ...], ...]  # per producer, one per bit


def bus_layout(framework_log_rows: Sequence[int], blocks: Sequence[BusBlock], producers: Sequence[Producer]) -> BusLayout:
    sizes = [*framework_log_rows, *(block.log_rows for block in blocks), *(p.log_rows for p in producers for _ in range(p.bits))]
    offsets, total = stack_offsets(sizes)
    depth = log2_ceil(total)
    placements = [Placement(size, offset) for size, offset in zip(sizes, offsets)]
    split = len(framework_log_rows) + len(blocks)
    bounds = accumulate((p.bits for p in producers), initial=split)
    by_producer = tuple(tuple(placements[start:end]) for start, end in pairwise(bounds))
    return BusLayout(depth, tuple(placements[: len(framework_log_rows)]), tuple(placements[len(framework_log_rows) : split]), by_producer)


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
    producers: tuple[tuple[E, ...], ...]  # per producer, the weight on each bit's block
    totals: tuple[E, E]  # what the tables and the producers owe each side, derived, short of RAM's image
    image: tuple[E, MultilinearPoint]  # RAM's image's weight in the push side's total, and its point
    alphas: tuple[E, ...]
    weights: tuple[E, ...]  # eq(alpha, .), the fingerprint the producers' public columns are made of
    beta: E


@dataclass(frozen=True)
class Column:
    """A committed column in a framework tuple: its value at the block's point is the prover's, read off the stream."""

    index: int


@dataclass(frozen=True)
class Image:
    """RAM's image in a framework tuple: only the program fixes it, so its value is left to the program's deferred claim."""


type FrameworkTuple = tuple[E | Column | Image, ...]
type FrameworkBlock = tuple[FrameworkTuple, FrameworkTuple]  # push, pull


def framework_tuples(layout: Layout, lows: dict[str, MultilinearPoint]) -> dict[str, FrameworkBlock]:
    """Each framework block's push and pull tuples at its point. Push starts the run and seeds every array; pull ends the
    run at the halt slot and finalizes every array with its committed columns. Register numbers and addresses are
    integers: register z is cell z, RAM's word z sits at RAM_BASE + 8z, the advice's at ADVICE_BASE + 8z."""

    def array(separator: E, index: E, initial: E | Column | Image, final_ts: str, final: str) -> FrameworkBlock:
        """A read-write array: every cell starts at the seed's timestamp holding `initial`, and ends at its last timestamp holding its final word."""
        return (separator, index, E(SEED_CLOCK), initial), (separator, index, Column(SHARED[final_ts]), Column(SHARED[final]))

    halt_pc = E(TEXT_BASE + 4 * (2**layout.log_bytecode - 1))  # the run ends on the text's last slot, which is never executed
    return {
        # cycle 1, then the halt slot at the announced clock, marked as an exit
        "state": ((SEP_STATE, E(layout.entry_pc), E(CLOCK_START), ZERO), (SEP_STATE, halt_pc, layout.final_clock, ONE)),
        # the registers start at zero, RAM as the statement has it, the advice as the prover has it
        "registers": array(SEP_REG, int_index_mle(0, 0, lows["registers"]), ZERO, "register_final_ts", "register_final"),
        "ram": array(SEP_MEM, int_index_mle(RAM_BASE, 3, lows["ram"]), Image(), "ram_final_ts", "ram_final"),
        "advice": array(SEP_MEM, int_index_mle(ADVICE_BASE, 3, lows["advice"]), Column(SHARED["advice_initial"]), "advice_final_ts", "advice_final"),
    }


def verify_bus_balance(layout: Layout, transcript: Transcript) -> BusResult:
    log_rows = layout.framework_log_rows
    framework_log_rows = tuple(log_rows[block] for block in FRAMEWORK)
    push_layout = bus_layout(framework_log_rows, layout.push, layout.producers)
    pull_layout = bus_layout(framework_log_rows, layout.pull, ())
    # Both trees run over the taller one's depth: the producers' bits push with no pull of their own.
    depth = max(push_layout.depth, pull_layout.depth)

    # A proof of work before the fingerprint challenges, for a program too large for the field alone; none otherwise.
    grinding = max(0, layout.log_bytecode - UNGROUND_LOG_BYTECODE)
    if grinding:
        transcript.grind_check(grinding)
    alphas = transcript.samples(BUS_BITS)
    weights = eq_kernel(alphas)
    beta = transcript.sample()
    point, tree_values = verify_gkr_grand_products(depth, transcript)

    lows = {block: tuple(point[: log_rows[block]]) for block in FRAMEWORK}
    tuples = framework_tuples(layout, lows)
    claims: list[ColumnClaim] = []
    opened: dict[int, E] = {}
    image_slots: dict[str, E] = {}  # per framework block, the fingerprint's weight on RAM's image, which is left out

    def fingerprint(block: str, coordinates: Sequence[E | Column | Image]) -> E:
        """The tuple's coordinates weighted by eq(alpha, .), slots past the ones named being zero. A committed column's
        value is read off the stream the first time either side names it, so push's columns come first, then pull's."""
        values = []
        for slot, coordinate in enumerate(coordinates):
            if isinstance(coordinate, Image):
                image_slots[block] = weights[slot]
                coordinate = ZERO
            elif isinstance(coordinate, Column):
                if coordinate.index not in opened:
                    opened[coordinate.index] = transcript.next_scalar()
                    claims.append(ColumnClaim(coordinate.index, lows[block], opened[coordinate.index]))
                coordinate = opened[coordinate.index]
            values.append(coordinate)
        return dot(weights[: len(values)], values)

    start = [fingerprint(block, tuples[block][0]) for block in FRAMEWORK]
    end = [fingerprint(block, tuples[block][1]) for block in FRAMEWORK]
    # RAM's image seeds the push side, at its block's selector.
    image = (push_layout.framework[FRAMEWORK.index("ram")].eq_above(point) * image_slots["ram"], lows["ram"])
    totals = []  # what the tables and the producers owe: settled at the bus point, or by the table sumcheck
    forms = tuple(tuple(Form() for _ in range(2)) for _ in TABLES)
    # A producer's bit block weighs on its own sumcheck, at its selector.
    producers = tuple(tuple(p.eq_above(point) for p in bits) for bits in push_layout.producers)
    for side, (blocks, side_layout, framework_fingerprints) in enumerate(((layout.push, push_layout, start), (layout.pull, pull_layout, end))):
        framework_selectors = [p.eq_above(point) for p in side_layout.framework]
        table_selectors = [p.eq_above(point) for p in side_layout.tables]
        known = dot(framework_selectors, [beta + fingerprint for fingerprint in framework_fingerprints])
        # A table's blocks stay symbolic: they accumulate into the form its columns settle, at the bus point or in the
        # table sumcheck.
        beta_form = _const(beta)
        for selector, block in zip(table_selectors, blocks, strict=True):
            form = forms[block.owner][side]
            form.add_scaled(beta_form, selector)
            for slot, coordinate in enumerate(block.coordinates):
                form.add_scaled(coordinate, selector * weights[slot])  # the fingerprint, one tuple slot at a time
        # Every occupied row holds its leaf; the rest of the leaf cube holds 1.
        producer_selectors = [selector for bits in producers for selector in bits] if side == 0 else []
        ones_padding = E.sum(framework_selectors + table_selectors + producer_selectors) + ONE
        totals.append(tree_values[side] + known + ones_padding)  # what the sumcheck owes: the GKR value, less framework and padding

    return BusResult(tuple(claims), point, forms, producers, (totals[0], totals[1]), image, tuple(alphas), tuple(weights), beta)


# Table sumcheck -------------------------------------------------------------


@dataclass(frozen=True)
class ProducerAir:
    """A producer in the table sumcheck: it owes the push side, for each bit i, sum_x eq(zeta, x) (1 + b_i(x) P'_i(x)) at
    its weight on that bit's block. Its bits are sent; of its public columns P'_i the verifier evaluates the part the
    program's columns do not enter, and leaves theirs to the program's deferred claim."""

    log_rows: int
    coefficients: tuple[E, ...]  # per bit, its block's weight, the push side's power folded in
    public: Callable[[MultilinearPoint], list[E]]  # the public columns P'_i at a point, short of the program's columns


@dataclass(frozen=True)
class TableSumcheck:
    claims: list[ColumnClaim]  # the column claims of the tables the bus point does not settle, short of their register numbers
    registers: list[tuple[MultilinearPoint, tuple[E, ...]]]  # per table, its point and its register numbers' bits there
    families: list[tuple[MultilinearPoint, tuple[E, ...]]]  # per producer, its point and its bits' values there
    twists: list[tuple[E, ...]]  # per producer, the weight of each bit's public column in the terminal identity
    residual: E  # what the terminal identity leaves to the program: the public columns' and the target's missing parts
    target_weight: E  # the weight of the target in the terminal identity: the product of the round challenges


def table_sumcheck(
    table_log_heights: Sequence[int],
    bus_forms: Sequence[Sequence[Form]],
    producers: Sequence[ProducerAir],
    form_powers: Sequence[E],
    identity_powers: Sequence[Sequence[E]],
    equality_point: MultilinearPoint,
    target: E,
    transcript: Transcript,
) -> TableSumcheck:
    """A table's summand is its two bus forms at `form_powers`, then its own identities, each at a power of its own:
    their sums are zero. A table the bus point settles keeps only its forms' part on its register numbers, the only
    columns it sends here."""
    heights = [*table_log_heights, *(producer.log_rows for producer in producers)]
    n_rounds = max(heights)
    challenges, claim = sumcheck(transcript, target, 4, [None] * n_rounds)
    point = list(reversed(challenges))
    weights = [ONE] * len(heights)
    for variable, challenge in enumerate(point):
        equality = ONE + equality_point[variable] + challenge
        for index, height in enumerate(heights):
            weights[index] *= equality if height > variable else challenge

    final = ZERO
    claims: list[ColumnClaim] = []
    registers = []
    for table, height, forms, own, weight in zip(TABLES, table_log_heights, bus_forms, identity_powers, weights[: len(TABLES)], strict=True):
        table_point = tuple(point[:height])
        if table.circuit is not None:
            numbers, slices = table.read_registers(transcript)
            final += weight * dot(form_powers, [form.on(numbers).evaluate(numbers.__getitem__) for form in forms])
        else:
            evaluations, slices = table.read_evaluations(transcript)
            final += weight * dot(form_powers, [form.evaluate(evaluations.__getitem__) for form in forms])
            final += weight * dot(own, [form.evaluate(evaluations.__getitem__) for form in table.identities])
            claims.extend(table.column_claims(table_point, evaluations))
        registers.append((table_point, slices))
    families = []
    twists = []
    for producer, weight in zip(producers, weights[len(TABLES) :], strict=True):
        bits = tuple(transcript.next_scalars(len(producer.coefficients)))
        producer_point = tuple(point[: producer.log_rows])
        public = producer.public(producer_point)
        final += weight * E.sum(c * (ONE + b * p) for c, b, p in zip(producer.coefficients, bits, public, strict=True))
        families.append((producer_point, bits))
        twists.append(tuple(weight * c * b for c, b in zip(producer.coefficients, bits, strict=True)))  # P'_i enters at c_i b_i
    return TableSumcheck(claims, registers, families, twists, final + claim, reduce(mul, challenges, ONE))


# The bus blocks no instruction table owns, which each side starts with, in this order: the run's boundary, then
# the read-write arrays.
FRAMEWORK = ("state", "registers", "ram", "advice")
# The read-only arrays, whose table side is a producer pushing each entry as often as it is read.
LOOKUPS = ("bytecode",)
# The committed columns no instruction table owns, each with the array whose rows it has: each read-write array's final
# words and timestamps, the advice's initial words, then how often each entry of the read-only array is read: entry
# x's word is that count as an integer, and its bits are its producer's one-bit columns. They come first in the global
# column numbering, then the packed flock witnesses (`FLOCKS`), then the tables' own columns, then each table's packed
# register numbers (`REGISTER_COLUMNS`).
SHARED_COLUMNS = (
    ("register_final", "registers"),
    ("register_final_ts", "registers"),
    ("ram_final", "ram"),
    ("ram_final_ts", "ram"),
    ("advice_initial", "advice"),
    ("advice_final", "advice"),
    ("advice_final_ts", "advice"),
    ("bytecode_mult", "bytecode"),
)
SHARED = {name: index for index, (name, _) in enumerate(SHARED_COLUMNS)}
NUM_FRAMEWORK_COLUMNS = len(SHARED_COLUMNS)

K_BITS = 64
FLOCK_K_SKIP = log2_ceil(K_BITS)
LOG_PACKING = log2_ceil(K_BITS)  # bits per committed K-element (pcs::pack::LOG_PACKING)
# Flock's zerocheck runs over a cube of at least this many variables: the skip, then seven fixed coordinates.
FLOCK_MIN_LOG_SIZE = 13

# The machine is RISC-V (rv64im). Instruction z sits at TEXT_BASE + 4z, and the register array holds x0..x31, then
# SINK, the cell an instruction with no destination writes: nothing reads it, which is what hardwires x0 to zero.
TEXT_BASE = 0x1000_0000
RAM_BASE = 0x4000_0000  # RAM's word z sits at RAM_BASE + 8z; the program's image is its first words
ADVICE_BASE = 0x2000_0000  # the advice's word z sits at ADVICE_BASE + 8z; what it holds before the run is the prover's
# What the regions hold at most, and the most rows a table may announce. These bound the counting arguments the
# memory and lookup proofs rest on, so the verifier checks them before it runs any reduction.
MAX_LOG_TEXT = 26
# The most bytecode entries, log2, whose bus keeps its margin over the commitment's list with no grinding. Each bit of
# entries past it doubles the bus's degree, so the bus grinds one bit for it before its fingerprint challenges.
UNGROUND_LOG_BYTECODE = 21
MAX_LOG_RAM = 27
MAX_LOG_ADVICE = 26
MAX_LOG_ROWS = 32
LOG_REGISTERS = 6
REGISTER_BITS = 5  # a register's number: x0..x31
SINK = 32
SYSCALL_REGISTER, SYS_EXIT = 17, 93  # a7 holds `exit` when the run halts
OUTPUT_REGISTERS = (10, 11, 12, 13)  # a0..a3, the public output


@dataclass(frozen=True)
class Layout:
    log_bytecode: int
    bytecode: Sequence[K]
    entry_pc: int
    log_ram: int
    log_advice: int
    ram: Sequence[tuple[int, Sequence[int]]]  # RAM before the run, as the stretches that are not zero
    push: tuple[BusBlock, ...]
    pull: tuple[BusBlock, ...]
    producers: tuple[Producer, ...]  # the bytecode's, then the two range arrays'
    placements: dict[int, Placement]  # every committed column's and every port's: a register number has none
    stack_log: int
    stack_lanes: int  # the level-0 lanes committed, the rest of each leaf being zero
    table_log_heights: tuple[int, ...]
    final_clock: E  # the timestamp the run ended on, announced by the prover

    @property
    def framework_log_rows(self) -> dict[str, int]:
        return framework_log_rows(self.log_bytecode, self.log_ram, self.log_advice)


def framework_log_rows(log_bytecode: int, log_ram: int, log_advice: int) -> dict[str, int]:
    """log2 of the rows of each framework block and of each lookup array: one per cell or entry of its array."""
    return {
        "state": 0,
        "registers": LOG_REGISTERS,
        "ram": log_ram,
        "advice": log_advice,
        "bytecode": log_bytecode,
    }


def _cols(columns: Sequence[str], *names: str) -> tuple[int, ...]:
    assert set(names) <= set(columns), f"unknown columns: {sorted(set(names) - set(columns))}"
    return tuple(columns.index(name) for name in names)


def _gpow(index: int) -> E:
    return GEN**index


def _const(value: E | int) -> Form:
    return Form({(): value if isinstance(value, E) else E(value)})


def _col(index: int) -> Form:
    return Form({(index,): ONE})


def _scaled(value: E, index: int) -> Form:
    return Form({(index,): value})


def _prod(a: int, b: int) -> Form:
    return Form({tuple(sorted((a, b))): ONE})


SEP_STATE = ONE
SEP_MEM = GEN
SEP_BYTECODE = GEN**2
SEP_REG = GEN**3

# The registers and RAM are read-write, ordered by a clock. A timestamp is the integer 2^40 | cycle << 5 | slot: bit 40,
# the live bit, is set on every tuple of the run and on the seeds, and clear on a padding row's, whose clock is zero.
# Access `slot` of a row with clock ts carries the timestamp ts ^ slot. A row reads rs1 and rs2, then writes rd last,
# after the RAM access of a load or a store; a row that skips an access leaves its slot unused. A hash row reads its
# two registers, then the sixteen words of its block.
LIVE_BIT = 40
SLOT_BITS = 5
CYCLE = 1 << SLOT_BITS
FAIL_BIT = LIVE_BIT + 1  # set in a row's step when one of its accesses is out of order
SEED_CLOCK = 1 << LIVE_BIT
CLOCK_START = SEED_CLOCK | CYCLE  # cycle 1, strictly after the seeds
REGISTER_SLOTS = (0, 1, 3)
RAM_SLOT = 2
HASH_WORDS = 16
HASH_OUT_WORD = 4  # the block's words 4 to 7 receive the result
HASH_SLOTS = tuple(range(2, 2 + HASH_WORDS))
EXT_LIMBS = 9  # an extension-field row's limbs: a's, b's, then c's, three each
EXT_SLOTS = tuple(range(REGISTER_SLOTS[2] + 1, REGISTER_SLOTS[2] + 1 + EXT_LIMBS))  # after its three register reads
EXT_OFFSET_LIMBS = (1, 2, 4, 5, 7, 8)  # the limbs at no pointer, p + 8 and p + 16, whose addresses the clock circuit computes
EXT_ACCUMULATE, EXT_BASE = 1, 2  # the flags: add the product to c, and read b as a base-field element
EXT_LEGAL_FLAGS = frozenset((0, EXT_ACCUMULATE, EXT_BASE, EXT_BASE | EXT_ACCUMULATE))
EXT_CLOCK_OUTPUTS = ("flag_bit_0", "flag_bit_1", *(f"limb_address_{k}" for k in EXT_OFFSET_LIMBS))  # the flags' bits, then the addresses


class Flushes:
    def __init__(self) -> None:
        self.push: list[tuple[Form, ...]] = []
        self.pull: list[tuple[Form, ...]] = []

    def pair(self, push: Sequence[Form], pull: Sequence[Form]) -> None:
        self.push.append(tuple(push))
        self.pull.append(tuple(pull))

    def state(self, columns: Sequence[str], npc: Form, exit_marker: Form) -> None:
        """Pull the current state and push the next: `npc`, a linear form of the row's columns, and the clock ts ^ step
        the row's clock circuit gives."""
        pc, ts, step = _cols(columns, "pc", "ts", "step")
        self.pair((_const(SEP_STATE), npc, _col(ts) + _col(step), exit_marker), (_const(SEP_STATE), _col(pc), _col(ts), _const(ZERO)))

    def read(self, entry: Sequence[Form]) -> None:
        """A read of a lookup array: one pull, which the array's own side pushes as often as it is read."""
        self.pull.append(tuple(entry))

    def access(self, columns: Sequence[str], separator: Form, address: Form, access: int, slot: int, old: Form, new: Form) -> None:
        """Access `access` of the row, at clock slot `slot`: pull the cell as its previous access left it, at the
        timestamp `prev`, and push it back at this access's own, ts ^ slot. The row's clock circuit orders the two."""
        ts, prev = _cols(columns, "ts", f"prev_{access}")
        self.pair((separator, address, _col(ts) + _const(slot), new), (separator, address, _col(prev), old))


# The instruction tables ------------------------------------------------------
#
# One table per instruction class, all of the same shape: the state step, the bytecode read, the register reads and
# the register write. What a class computes is a flock circuit, and every word that circuit reads or writes (`WORDS`)
# is a column here that lives in the circuit's packed witness: the bus is what binds the circuit to the machine. A row
# reads rs2 only if its circuit takes v2, and writes rd only if its circuit gives out: a load's rs2 is x0, and a store's
# and a hash's rd is the sink, so those accesses would prove nothing. A doubleword load or store (`copies`) is the
# exception: its circuit gives the address alone, and the word it moves is a column of its own, the cell that rd
# receives or the v2 that the cell receives. The hash class also accesses the sixteen words of its block, the result's
# four rewritten.
#
# The extension-field class has no class circuit. Its row reads rd as an address (`vd`), then nine limbs, committed
# columns: a's and b's read, c's rewritten. A base-field b's two high limbs are reads of x0. Its table's identities say
# the product, and its clock circuit splits the flags into their bits and computes the addresses of the limbs at no
# pointer.

CONTROL_COLUMNS = ("dt", "jump", "exit")  # a class with jumps: the bytecode's offset, the circuit's gated jump, the exit
HASH_COLUMNS = (*(f"cell_{k}" for k in range(HASH_WORDS)), *(f"cell_new_{HASH_OUT_WORD + j}" for j in range(4)))
EXT_COLUMNS = (
    *(f"limb_{k}" for k in range(EXT_LIMBS)),
    *(f"limb_new_{k}" for k in range(6, EXT_LIMBS)),
    *(f"limb_address_{k}" for k in EXT_OFFSET_LIMBS),
)
RAM_COLUMNS = {"none": (), "read": ("address", "cell_0"), "write": ("address", "cell_0", "cell_new_0"), "block": HASH_COLUMNS, "limbs": EXT_COLUMNS}


EXIT_SLOT = 11  # public selector: only ECALL can terminate the state channel
BAD_SLOT = 10  # where a bytecode tuple holds a row's `bad` word: past every field of an entry, where the program is zero
BYTECODE_PUBLIC_SLOT = 2  # an entry's first field, after the separator and the address


def _registers(ram: str, words: Sequence[str | None], copies: bool) -> tuple[bool, bool]:
    """Whether a row reads rs2 and writes rd: when its circuits take v2 and give out, or when it is a doubleword store
    reading the v2 it moves, or a doubleword load writing the cell it moves."""
    return "v2" in words or (copies and ram == "write"), "out" in words or (copies and ram == "read")


def _class_columns(control: bool, ram: str, words: Sequence[str | None], copies: bool) -> tuple[str, ...]:
    reads_rs2, writes_rd = _registers(ram, words, copies)
    # A doubleword store's new cell is its v2 column.
    ram_columns = RAM_COLUMNS[ram][:2] if copies else RAM_COLUMNS[ram]
    flag_bits = tuple(word for word in words if word and word.startswith("flag_bit_"))
    return (
        "pc", "ts", "a1", "pc4", "v1", *(("flags",) if "flags" in words else ()), *(("a2", "v2") if reads_rs2 else ()),
        *(("ad", "vd_old") if writes_rd else ()), *(("out",) if "out" in words else ()), *(("ad", "vd") if "vd" in words else ()),
        *(CONTROL_COLUMNS if control else ()), *(("imm",) if "imm" in words else ()), *ram_columns, *flag_bits, *(("bad",) if "bad" in words else ()),
        *(f"prev_{i}" for i in range(len(_slots(ram, reads_rs2, writes_rd or "vd" in words)))), "step",
    )  # fmt: skip


def _slots(ram: str, reads_rs2: bool, touches_rd: bool) -> tuple[int, ...]:
    """The clock slots of a row's accesses, in the order of their columns: the registers' it makes, then RAM's."""
    registers = tuple(slot for slot, made in zip(REGISTER_SLOTS, (True, reads_rs2, touches_rd), strict=True) if made)
    if ram == "block":
        return (*registers, *HASH_SLOTS)
    if ram == "limbs":
        return (*registers, *EXT_SLOTS)
    return (*registers, RAM_SLOT) if RAM_COLUMNS[ram] else registers


def _class_flushes(opcode: int, columns: Sequence[str], control: bool, ram: str, words: Sequence[str | None], copies: bool) -> Flushes:
    reads_rs2, writes_rd = _registers(ram, words, copies)
    a1, pc4, v1 = _cols(columns, "a1", "pc4", "v1")
    # A row without flags, an rs2 read, an rd write or an immediate reads their constants off the entry: zero, x0, the
    # sink, and zero.
    npc, vd, fields, exit_selector = _col(pc4), _const(ZERO), (), _const(ZERO)
    flags_form, a2_form, ad_form, imm_form = _const(ZERO), _const(ZERO), _const(SINK), _const(ZERO)
    if "flags" in words:
        flags_form = _col(_cols(columns, "flags")[0])
    if reads_rs2:
        a2_form = _col(_cols(columns, "a2")[0])
    if writes_rd:
        # What rd receives: the circuit's result (a jump's link), or the cell a doubleword load moves.
        ad, out = _cols(columns, "ad", "cell_0" if copies else "out")
        ad_form, vd = _col(ad), _col(out)
    if "vd" in words:
        ad_form = _col(_cols(columns, "ad")[0])
    if "imm" in words:
        imm_form = _col(_cols(columns, "imm")[0])
    if control:
        # The next pc is pc + 4 plus the circuit's jump: the bytecode's offset when a fixed jump is taken, the sum XOR
        # pc + 4 for an indirect one. Only an exit marks its next state, which only the final state meets.
        dt, jump, exit = _cols(columns, *CONTROL_COLUMNS)
        npc, fields, exit_selector = _col(pc4) + _col(jump), (_col(dt),), _col(exit)
    flushes = Flushes()
    flushes.state(columns, npc, exit_selector)
    entry = (_const(_gpow(opcode)), flags_form, _col(a1), a2_form, ad_form, imm_form, _col(pc4), *fields)
    if "bad" in words:
        # What the circuit asserts to be zero rides a slot where the program is zero, so the lookup makes it zero.
        entry = (*entry, *[_const(ZERO)] * (BAD_SLOT - BYTECODE_PUBLIC_SLOT - len(entry)), _col(_cols(columns, "bad")[0]))
    entry = (*entry, *[_const(ZERO)] * (EXIT_SLOT - BYTECODE_PUBLIC_SLOT - len(entry)), exit_selector)
    flushes.read((_const(SEP_BYTECODE), _col(_cols(columns, "pc")[0]), *entry))
    # The register's number comes straight from the bytecode. A read pushes back the value it pulled. The accesses'
    # columns are numbered in the order the row makes them.
    accesses = count()
    flushes.access(columns, _const(SEP_REG), _col(a1), next(accesses), REGISTER_SLOTS[0], _col(v1), _col(v1))
    if reads_rs2:
        v2 = _col(_cols(columns, "v2")[0])
        flushes.access(columns, _const(SEP_REG), a2_form, next(accesses), REGISTER_SLOTS[1], v2, v2)
    if writes_rd:
        flushes.access(columns, _const(SEP_REG), ad_form, next(accesses), REGISTER_SLOTS[2], _col(_cols(columns, "vd_old")[0]), vd)
    if "vd" in words:
        # An address in rd, read and written back as found.
        pointer = _col(_cols(columns, "vd")[0])
        flushes.access(columns, _const(SEP_REG), ad_form, next(accesses), REGISTER_SLOTS[2], pointer, pointer)
    if ram in ("read", "write"):
        # The cell's address is the circuit's word, so an access outside RAM, or a misaligned one, pulls a tuple nothing
        # pushed. A doubleword store leaves its v2 column there, the one its rs2 read pulls.
        new = "v2" if copies and ram == "write" else RAM_COLUMNS[ram][-1]
        address, cell, cell_new = _cols(columns, "address", "cell_0", new)
        flushes.access(columns, _const(SEP_MEM), _col(address), next(accesses), RAM_SLOT, _col(cell), _col(cell_new))
    if ram == "block":
        # Word k of the block is the cell at v1 ^ 8k, which is v1 + 8k in the field; the result's words are rewritten.
        for k in range(HASH_WORDS):
            old = _col(_cols(columns, f"cell_{k}")[0])
            new = _col(_cols(columns, f"cell_new_{k}")[0]) if HASH_OUT_WORD <= k < HASH_OUT_WORD + 4 else old
            flushes.access(columns, _const(SEP_MEM), _col(v1) + _const(8 * k), next(accesses), HASH_SLOTS[k], old, new)
    if ram == "limbs":
        # Each operand's first limb is at its pointer, the others at the addresses the clock circuit computes; c's are
        # rewritten. A base-field b's high limbs are reads of x0, at the address zero the clock circuit gives them,
        # under the separator SEP_MEM + base (SEP_MEM + SEP_REG), which the bit `base` picks.
        pointers = (v1, *_cols(columns, "v2", "vd"))
        (base,) = _cols(columns, "flag_bit_1")
        for k in range(EXT_LIMBS):
            operand, limb = divmod(k, 3)
            separator = _const(SEP_MEM)
            if operand == 1 and limb:
                separator += _scaled(SEP_MEM + SEP_REG, base)
            address = _col(_cols(columns, f"limb_address_{k}")[0]) if limb else _col(pointers[operand])
            old = _col(_cols(columns, f"limb_{k}")[0])
            new = _col(_cols(columns, f"limb_new_{k}")[0]) if k >= 6 else old
            flushes.access(columns, separator, address, next(accesses), EXT_SLOTS[k], old, new)
    return flushes


def _ext_identities(columns: Sequence[str]) -> tuple[Form, ...]:
    """The extension-field table's identities: with d_m the sum of a_j b_k over j + k = m (products in K), the
    reduction y^3 = y + 1, y^4 = y^2 + y has its coefficients in GF(2), so each new limb is a sum of K products,
    c'_0 = accumulate c_0 + d_0 + d_3, c'_1 = accumulate c_1 + d_1 + d_3 + d_4 and c'_2 = accumulate c_2 + d_2 + d_4.
    Each form is the difference of the two sides: it vanishes on a row exactly when its new limb is the product."""
    (keep,) = _cols(columns, "flag_bit_0")
    limbs = _cols(columns, *(f"limb_{k}" for k in range(EXT_LIMBS)))
    forms = []
    for i in range(3):
        form = _col(_cols(columns, f"limb_new_{6 + i}")[0]) + _prod(keep, limbs[6 + i])
        for j, k in product(range(3), repeat=2):
            if j + k == i or (j + k == 3 and i < 2) or (j + k == 4 and i > 0):
                form += _prod(limbs[j], limbs[3 + k])
        forms.append(form)
    return tuple(forms)


@dataclass(frozen=True)
class Table:
    """One instruction class's table: its columns, its bus flushes, its class circuit and its clock circuit."""

    name: str
    opcode: int  # also its index in TABLES, so g^opcode is its bytecode tag
    control: bool
    ram: str  # how the class uses RAM: a key of RAM_COLUMNS
    circuit: FlockCircuit | None  # None for the class its table proves by identities
    ports: tuple[str | None, ...]  # the circuit's port words in order: a column each, or None for a hint, which is no column
    legal_flags: frozenset[int]
    copies: bool = False  # a doubleword load or store: the word moved is a column of its own, not a circuit word
    clock_inputs: tuple[str, ...] = ()  # what the clock circuit reads past the timestamps, and gives past the step
    clock_outputs: tuple[str, ...] = ()
    clock_gates: Callable[[Sequence[int]], _GateList] = lambda slots: _clock(slots)

    @property
    def words(self) -> tuple[str | None, ...]:
        """Every word of the table's circuits: its class circuit's, then its clock circuit's own."""
        return (*self.ports, *self.clock_inputs, *self.clock_outputs)

    @property
    def columns(self) -> tuple[str, ...]:
        return _class_columns(self.control, self.ram, self.words, self.copies)

    @property
    def flushes(self) -> Flushes:
        return _class_flushes(self.opcode, self.columns, self.control, self.ram, self.words, self.copies)

    @property
    def identities(self) -> tuple[Form, ...]:
        """The forms the table's rows all make zero, over its columns: the extension-field product's three."""
        return _ext_identities(self.columns) if self.ram == "limbs" else ()

    @property
    def slots(self) -> tuple[int, ...]:
        return _slots(self.ram, self.reads_rs2, self.writes_rd or self.reads_rd)

    @property
    def reads_rs2(self) -> bool:
        return _registers(self.ram, self.words, self.copies)[0]

    @property
    def writes_rd(self) -> bool:
        return _registers(self.ram, self.words, self.copies)[1]

    @property
    def reads_rd(self) -> bool:
        """Whether the row reads rd as an address rather than writing it."""
        return "vd" in self.words

    @cached_property
    def clock(self) -> FlockCircuit:
        return self.clock_gates(self.slots).circuit()

    @property
    def clock_ports(self) -> tuple[str, ...]:
        return ("ts", *(f"prev_{i}" for i in range(len(self.slots))), *self.clock_inputs, "step", *self.clock_outputs)

    @property
    def width(self) -> int:
        return len(self.columns)

    @property
    def registers(self) -> tuple[tuple[int, int], ...]:
        """The register numbers a row reads off its entry, a1, then a2 and ad where it has them, each with its width:
        not committed, but packed in this order into a committed word (`register_words`), which the opening reads bit by
        bit. A register read is below 32, five bits; a cell written may be the sink, 32, six bits."""
        fields = (("a1", REGISTER_BITS), *((("a2", REGISTER_BITS),) if self.reads_rs2 else ()))
        if self.writes_rd:
            fields += (("ad", LOG_REGISTERS),)
        elif self.reads_rd:
            fields += (("ad", REGISTER_BITS),)
        return tuple((_cols(self.columns, name)[0], width) for name, width in fields)

    def read_registers(self, transcript: Transcript) -> tuple[dict[int, E], tuple[E, ...]]:
        """Its register numbers' evaluations at the table sumcheck's point, by column, and their bits' there: each number's
        bits are sent. Bit b of an integer is x^b, so a number's evaluation is sum_b x^b slice_b."""
        slices = tuple(transcript.next_scalars(sum(width for _, width in self.registers)))
        numbers, start = {}, 0
        for local, width in self.registers:
            numbers[local] = E.sum(E(1 << bit) * slice for bit, slice in enumerate(slices[start : start + width]))
            start += width
        return numbers, slices

    def read_evaluations(self, transcript: Transcript) -> tuple[tuple[E, ...], tuple[E, ...]]:
        """Its columns' evaluations at the table sumcheck's point, and its register numbers' bits there: every column's but
        the numbers' is sent, then the numbers' bits."""
        sent = iter(transcript.next_scalars(self.width - len(self.registers)))
        numbers, slices = self.read_registers(transcript)
        return tuple(numbers[local] if local in numbers else next(sent) for local in range(self.width)), slices

    def column_claims(self, point: MultilinearPoint, evaluations: Sequence[E]) -> list[ColumnClaim]:
        """Its columns' claims at `point`, short of its register numbers, whose bits are their word's claim."""
        numbers = {local for local, _ in self.registers}
        base = GLOBAL_COLUMN_BASES[self.opcode]
        return [ColumnClaim(base + local, point, value) for local, value in enumerate(evaluations) if local not in numbers]

    @property
    def min_log_height(self) -> int:
        """A batch is at least eight instances, and the zerocheck's cube at least 2^13 bits, for each of its circuits."""
        return max(3, FLOCK_MIN_LOG_SIZE - min(c.log_size for c in (self.circuit, self.clock) if c))


def slot_bits(circuit: FlockCircuit) -> int:
    """log2 of the packed words one instance of a circuit occupies."""
    return circuit.log_size - LOG_PACKING


# WHIR opening ----------------------------------------------------------------

INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 4
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3
RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1
RESIDUAL_MAX_LOG = 5
QUERY_GRINDING_BITS = 17

MIN_STACKED_LOG = 15
MAX_STACKED_LOG = 28

WHIR_QUERIES = (((222,55), (223,56,30), (223,56,31), (223,56,32), (223,56,32), (223,56,32,22), (223,56,32,22), (224,56,32,23), (224,56,32,23), (224,56,32,23,17), (224,56,32,23,17), (224,56,32,23,18), (225,56,32,23,18), (225,56,32,23,18,14)), ((111,45), (112,45,27), (112,45,28), (112,45,28), (112,45,28), (112,45,28,20), (112,45,28,20), (112,45,28,21), (112,45,28,21), (112,45,28,21,16), (112,45,28,21,16), (112,45,28,21,16), (112,45,28,21,16), (112,45,28,21,16,13)), ((75,37), (75,37,24), (75,37,25), (75,38,25), (75,38,25), (75,38,25,18), (75,38,25,19), (75,38,25,19), (75,38,25,19), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15,13)), ((56,32), (56,32,22), (56,32,22), (56,32,23), (56,32,23), (56,32,23,17), (56,32,23,17), (56,32,23,18), (56,32,23,18), (56,32,23,18,14), (56,32,23,18,14), (56,32,23,18,14), (56,32,23,18,15), (56,32,23,18,15,12)))  # fmt: skip


@dataclass(frozen=True)
class WhirConfig:
    log_inv_rates: tuple[int, ...]
    folds: tuple[int, ...]
    queries: tuple[int, ...]
    grinding_bits: tuple[int, ...]
    ood_samples: tuple[int, ...]


def derive_config(log_n: int, log_inv_rate: int) -> WhirConfig:
    """The opening shape at this size and rate: the ladder geometry, then the tabulated query counts, the same grinding at every level, and one OOD sample at every level past L0."""
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
    return WhirConfig(
        log_inv_rates=tuple(log_inv_rates),
        folds=tuple(folds),
        queries=queries,
        grinding_bits=(QUERY_GRINDING_BITS,) * len(folds),
        ood_samples=(0,) + (1,) * (len(folds) - 1),
    )


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


def verify_whir(
    transcript: Transcript, log_n: int, n_lanes: int, log_inv_rate: int, target: E, root: Digest, evaluate_basis: Callable[[Sequence[E]], E]
) -> None:
    """Verify the base-field multilevel opening with a one-point terminal check. Only `n_lanes` of the witness's level-0
    lanes are committed: the others lead every level-0 leaf as zeros."""
    config = derive_config(log_n, log_inv_rate)
    levels = len(config.folds)

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
            running_quad = transcript.sumcheck_round_poly(3, poly_eval(running_quad, challenge))

        message_log = log_n - len(folds)
        final_level = level == levels - 1
        # The level's claims, held until its batching challenge is drawn: the
        # OOD claims first, then the query batch (Annex B, Protocol 1 step 1).
        pending: list[tuple[Sequence[E], Callable[[Sequence[E]], E]]] = []
        if final_level:
            residual = tuple(transcript.next_scalars(2**message_log))
        else:
            next_root = Digest.from_halves(*transcript.next_scalars(2))
            for _ in range(config.ood_samples[level + 1]):
                ood_point = tuple(transcript.samples(message_log))
                ood_value = transcript.next_scalar()
                pending.append((transcript.sumcheck_round_poly(3, ood_value), lambda x, z=ood_point: eq_eval(z, x)))

        transcript.grind_check(config.grinding_bits[level])
        block_length = 2 ** (message_log + level_rate)
        queries = sample_queries(transcript, block_length, config.queries[level])
        # One batching challenge per level, drawn once every claim it batches is
        # fixed: the OOD claims above and these query positions.
        lam = transcript.sample()
        query_weights = powers(lam, len(queries))
        # Level 0 committed the K witness, one leaf word per lane, lanes descending so
        # that the absent ones lead the leaf; every deeper level a folded E one, three
        # words per lane.
        lanes = 2**fold_count
        rows: list[Sequence[K | E]]
        if level == 0:
            words = transcript.merkle(current_root, block_length, queries, lanes, zero_prefix=lanes - n_lanes)
            rows = [tuple(reversed(row)) for row in words]
        else:
            rows = [_ext_row(row) for row in transcript.merkle(current_root, block_length, queries, 3 * lanes)]
        enforced = _enforced_sum(rows, level_folds, query_weights)

        # Every commitment, including the last one, enters through an intro
        # message; the level's claims are then batched with powers of `lam`,
        # the running claim keeping lam^0 = 1.
        batch = (message_log, tuple(queries), tuple(query_weights))
        pending.append((transcript.sumcheck_round_poly(3, enforced), lambda x, b=batch: _induced_weight(*b, x)))
        scalar = ONE
        for intro, weight_at in pending:
            scalar *= lam
            running_quad = [q + scalar * i for q, i in zip(running_quad, intro, strict=True)]
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
            point = folds + tail_folds
            lane_folds = config.folds[0]
            weight = evaluate_basis(point[lane_folds:] + point[:lane_folds])
            for claim in glued:
                weight += claim.scalar * claim.weight_at(folds[claim.fold_start :] + tail_folds)
            terminal = weight * multilinear_eval(residual, tail_folds)
            require(terminal == running_target, "WHIR terminal check failed")
            return
        current_root = next_root

    raise VerificationError("WHIR verification ended without a terminal level")


# Flock reduction -------------------------------------------------------------

PHI_BASIS = (E(0x0000000000000001), E(0x033CE8BEDDC8A656), E(0x512620375ED2A108), E(0x0C9E636090AAFC01), E(0xBA4F3CD82801769C), E(0xBA26E7904ADB4A47), E(0x467698598926DC01), E(0x4418AE808B28BDD0))  # fmt: skip
PHI = tuple(E.sum(PHI_BASIS[bit] for bit in range(8) if value >> bit & 1) for value in range(256))

_MEDIUM_GENERATOR = E(0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0)

FIXED_CHALLENGES = (
    PHI[0xF7], PHI[0x53], PHI[0xB5],
    *tuple(_MEDIUM_GENERATOR ** (2**power) / (ONE + _MEDIUM_GENERATOR ** (2**power)) for power in range(4)),
)  # fmt: skip


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


def interpolate_zero_on_skip(values_on_coset: Sequence[E], point: E) -> E:
    """At `point`, the polynomial of degree below `2 * K_BITS` that is zero on `PHI[:K_BITS]` and `values_on_coset` on `PHI[K_BITS : 2 * K_BITS]`.

    Over the whole window the zeros drop out of the Lagrange sum, and every weight left carries `prod_(s in PHI[:K_BITS]) (point + s)`.
    `total` and `prefix` are the sum and the product of the differences over the nodes seen so far."""
    vanishing = reduce(mul, (point + node for node in PHI[:K_BITS]), ONE)
    total, prefix = ZERO, vanishing * _window_denominator(2 * K_BITS)
    for node, value in zip(PHI[K_BITS : 2 * K_BITS], values_on_coset, strict=True):
        difference = point + node
        total = total * difference + value * prefix
        prefix *= difference
    return total


@dataclass(frozen=True)
class ZerocheckResult:
    z_skip: E
    chi: MultilinearPoint
    v_a: E
    v_b: E
    v_c: E


def verify_flock_zerocheck(log_sizes: Sequence[int], transcript: Transcript) -> list[ZerocheckResult]:
    """The zerocheck of every circuit at once, under shared challenges: one univariate skip round, then quadratic
    rounds on the batch, circuit f weighted by lambda^f. C rides those rounds with AB, so each circuit's three claims
    come out at one point: z_skip and the first log_size - k_skip round challenges. A circuit done before a round adds
    the value it ended on, which the round's claim alone carries."""
    n_rounds = max(log_sizes) - FLOCK_K_SKIP
    # The point r: seven fixed coordinates, the rest sampled; circuit f uses its first log_size - k_skip.
    r = (*FIXED_CHALLENGES, *transcript.samples(n_rounds - len(FIXED_CHALLENGES)))
    lambdas = powers(transcript.sample(), len(log_sizes))

    # sum_f lambda^f P_f on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    p_coset = transcript.next_scalars(K_BITS)
    z_skip = transcript.sample()
    v_p = interpolate_zero_on_skip(p_coset, z_skip)

    # The quadratic rounds on the batch, closed by every circuit's v_a, v_b, v_c.
    chi, running = sumcheck(transcript, v_p, 3, r)
    results = []
    for log_size in log_sizes:
        v_a, v_b, v_c = transcript.next_scalars(3)
        results.append(ZerocheckResult(z_skip, chi[: log_size - FLOCK_K_SKIP], v_a, v_b, v_c))
    require(dot(lambdas, [zc.v_a * zc.v_b + zc.v_c for zc in results]) == running, "Flock zerocheck terminal mismatch")
    return results


@dataclass(frozen=True)
class FlockCircuit:
    """What the reduction needs of a circuit: its block size, where its constant wire sits, and the walk that
    evaluates `e_row^T (A0 + alpha B0) w_col` without building either matrix."""

    log_size: int
    constant_column: int
    bilinear: Callable[[E, Sequence[E], Sequence[E]], E]


@dataclass(frozen=True)
class MatrixForm:
    """The part of a lincheck's terminal identity only the circuit fixes: `e_row^T (A0 + alpha B0) w_col`, e_row the
    quirky eq weights at (z_skip, chi_in) and w_col the column weights eq(chi_in_prime, .) times the 64 slices s."""

    alpha: E
    z_skip: E
    chi_in: MultilinearPoint
    chi_in_prime: MultilinearPoint
    s: tuple[E, ...]

    def evaluate(self, circuit: FlockCircuit) -> E:
        # e_row: phi8 Lagrange in the skip coordinate, eq in the slot variables.
        e_row = [weight * value for weight in eq_kernel(self.chi_in) for value in lagrange_weights(K_BITS, self.z_skip)]
        w_col = [value * weight for weight in eq_kernel(self.chi_in_prime) for value in self.s]
        return circuit.bilinear(self.alpha, e_row, w_col)


def verify_flock_lincheck(
    circuits: Sequence[FlockCircuit], zerochecks: Sequence[ZerocheckResult], transcript: Transcript
) -> list[tuple[MultilinearPoint, tuple[E, ...], MatrixForm, E]]:
    """Lincheck for every circuit under one alpha and one sumcheck, circuit f's identity weighted by alpha^(4f). Its
    rounds bind each circuit's high column coordinates, top first, every circuit from the first round; a circuit done
    before a round carries the line its lifting variable makes. Per circuit: its claim's point, then its 64 slices s,
    then the circuit's matrix form and the value the prover sends for it, which the terminal identity needs it to take."""
    alpha = transcript.sample()  # batches the two matrix identities, the c claim and the constant-position claim, and the circuits
    weights = powers(alpha**4, len(circuits))
    rounds = [circuit.log_size - FLOCK_K_SKIP for circuit in circuits]
    claim = dot(weights, [zc.v_a + alpha * zc.v_b + alpha**2 * zc.v_c + alpha**3 for zc in zerochecks])
    round_challenges, r_lc = sumcheck(transcript, claim, 3, [None] * max(rounds))

    # Every residual and its matrix form's value, then the terminal identity: each circuit's form, c term and pin term.
    # C = I, so the c weight is e_row itself, and both sides being tensors it collapses to eq(chi_in, chi_in_prime)
    # times a 64-term Lagrange combination; the pin's column weight is its slice times the eq weight of its slot.
    terminal = ZERO
    results = []
    for circuit, zc, n_rounds, weight in zip(circuits, zerochecks, rounds, weights, strict=True):
        s = tuple(transcript.next_scalars(K_BITS))
        value = transcript.next_scalar()
        chi_in = zc.chi[:n_rounds]
        chi_in_prime = tuple(reversed(round_challenges[:n_rounds]))
        pin = circuit.constant_column
        own = (
            value
            + alpha**2 * eq_eval(chi_in, chi_in_prime) * dot(lagrange_weights(K_BITS, zc.z_skip), s)
            + alpha**3 * s[pin % K_BITS] * eq_kernel(chi_in_prime)[pin // K_BITS]
        )
        terminal += reduce(mul, round_challenges[n_rounds:], weight) * own
        results.append((chi_in_prime + zc.chi[n_rounds:], s, MatrixForm(alpha, zc.z_skip, chi_in, chi_in_prime, s), value))
    require(terminal == r_lc, "Flock lincheck terminal mismatch")
    return results


# The class circuits ----------------------------------------------------------
#
# One instance is the circuit's ports, whole 64-bit words each (the inputs, then the outputs), then the constant
# wire, then the circuit's products in the order they are made. A circuit is a gate list, a wire being the gate that
# drives it: a free committed wire (an input bit or the constant), an uncommitted XOR, an AND whose product is
# committed at a slot, or a copy that commits an affine wire at a slot, which is how a result leaves. A port bit with
# no gate is an empty row, hence zero. What has to agree with the prover is the port layout and the order products are
# made in; the order of the XORs is free.

type Gate = tuple[str, int, int, int]
type Wire = int | None  # None is a structural zero


class _GateList:
    def __init__(self, input_bits: Sequence[int | range], output_bits: Sequence[int]) -> None:
        """An input port given as a range is range.stop bits wide, its bits below the range structural zeros, which
        their empty rows force to zero."""
        self.gates: list[Gate] = []
        ranges = [bits if isinstance(bits, range) else range(bits) for bits in input_bits]
        words = [-(-bits // 64) for bits in (*(r.stop for r in ranges), *output_bits)]
        self.constant_column = 64 * sum(words)
        self.next_slot = self.constant_column + 1
        self.one: Wire = self.push("free", self.constant_column)
        bases = [64 * sum(words[:port]) for port in range(len(words))]
        self.inputs: list[list[Wire]] = [
            [self.push("free", base + i) if i in bits else None for i in range(bits.stop)] for base, bits in zip(bases, ranges)
        ]
        self.output_bases = bases[len(input_bits) :]

    @property
    def log_size(self) -> int:
        return log2_ceil(self.next_slot)

    def push(self, kind: str, x: int, y: int = 0, slot: int = 0) -> int:
        self.gates.append((kind, x, y, slot))
        return len(self.gates) - 1

    def xor(self, x: Wire, y: Wire) -> Wire:
        if x is None or y is None:
            return y if x is None else x
        return self.push("xor", x, y)

    def invert(self, x: Wire) -> Wire:
        return self.xor(x, self.one)

    def product(self, x: Wire, y: Wire) -> Wire:
        """One product, and one slot, unless an operand is a structural zero."""
        if x is None or y is None:
            return None
        self.next_slot += 1
        return self.push("and", x, y, self.next_slot - 1)

    def either(self, x: Wire, y: Wire) -> Wire:
        both = self.product(x, y)
        return self.xor(self.xor(x, y), both)

    def mux(self, select: Wire, x: Wire, y: Wire) -> Wire:
        """`x if select else y`, one product."""
        return self.xor(self.product(select, self.xor(x, y)), y)

    def output(self, port: int, bit: int, wire: Wire) -> None:
        if wire is not None:
            self.push("copy", wire, 0, self.output_bases[port] + bit)

    def and_output(self, port: int, bit: int, x: Wire, y: Wire) -> Wire:
        """One product, committed as bit `bit` of output port `port` rather than at the next slot: no copy."""
        if x is None or y is None:
            return None
        return self.push("and", x, y, self.output_bases[port] + bit)

    def bilinear(self, alpha: E, row_weights: Sequence[E], column_weights: Sequence[E]) -> E:
        """`e_row^T (A0 + alpha B0) w_col` by one forward walk: every committed wire is a row, whose A side is the
        wire's expansion against `w_col` and whose B side is its other factor, the constant for a free wire or a copy."""
        constant = column_weights[self.constant_column]
        left, right = [ZERO] * 2**self.log_size, [ZERO] * 2**self.log_size
        wires: list[E] = []
        for kind, x, y, slot in self.gates:
            if kind == "xor":
                wires.append(wires[x] + wires[y])
                continue
            slot = x if kind == "free" else slot
            left[slot] = column_weights[slot] if kind == "free" else wires[x]
            right[slot] = wires[y] if kind == "and" else constant
            wires.append(column_weights[slot])
        return dot(row_weights, left) + alpha * dot(row_weights, right)

    def circuit(self) -> FlockCircuit:
        return FlockCircuit(self.log_size, self.constant_column, self.bilinear)


# The ALU class's selector bits, one-hot where they select. `b` is `v2 ^ imm`, one of the two being zero.
ALU_SUB, ALU_WORD, ALU_LT, ALU_LTU, ALU_AND, ALU_OR, ALU_XOR, ALU_INDIRECT = range(8)
ALU_BRANCHES = ALU_EQ, ALU_NE, ALU_BLT, ALU_BGE, ALU_BLTU, ALU_BGEU = range(8, 14)
ALU_ALWAYS = 14
ALU_LEGAL_FLAGS = frozenset(
    sum(1 << bit for bit in bits)
    for bits in [(), (ALU_SUB,), (ALU_WORD,), (ALU_SUB, ALU_WORD), (ALU_AND,), (ALU_OR,), (ALU_XOR,), (ALU_INDIRECT, ALU_ALWAYS), (ALU_ALWAYS,)]
    + [(ALU_SUB, bit) for bit in (ALU_LT, ALU_LTU, *ALU_BRANCHES)]
)


def _alu() -> _GateList:
    """(v1, v2, imm, flags, dt, pc4) -> (out, jump): add or subtract (and the 32-bit forms), the two comparisons, AND, OR,
    XOR, the six branch conditions, the jumps. `v1 - b` is `v1 + not(b) + 1`, which borrows exactly when it does not carry
    out. An indirect jump (jalr) outputs its link pc4 and offsets the successor by its sum XOR pc4, bit 0 left out, so
    it lands on the sum with bit 0 cleared. `jump` is that offset added to `dt` when the jump is taken and zero
    otherwise, each bit a product written at its output position."""
    c = _GateList((64, 64, 64, 15, 64, 64), (64, 64))
    v1, v2, imm, flags, dt, pc4 = c.inputs
    b = [c.xor(x, y) for x, y in zip(v2, imm)]
    carry = flags[ALU_SUB]
    total: list[Wire] = []
    for x, y in zip(v1, b):
        y = c.xor(y, flags[ALU_SUB])
        xc, yc = c.xor(x, carry), c.xor(y, carry)
        total.append(c.xor(xc, y))
        carry = c.xor(c.product(xc, yc), carry)
    ltu = c.invert(carry)
    lt = c.xor(ltu, c.xor(v1[63], b[63]))
    diff = [c.xor(x, y) for x, y in zip(v1, b)]
    ne = reduce(c.either, diff, None)
    eq = c.invert(ne)

    # `out`: the sum (its low 32 bits sign-extended if asked) unless a selector is set. OR is AND plus XOR.
    total = total[:32] + [c.mux(flags[ALU_WORD], total[31], bit) for bit in total[32:]]
    none = reduce(c.xor, (flags[bit] for bit in (ALU_LT, ALU_LTU, ALU_AND, ALU_OR, ALU_XOR)), c.one)
    and_or, or_xor = c.xor(flags[ALU_AND], flags[ALU_OR]), c.xor(flags[ALU_OR], flags[ALU_XOR])
    out = [c.product(none, bit) for bit in total]
    for i in range(64):
        both = c.product(v1[i], b[i])
        and_term = c.product(and_or, both)
        out[i] = c.xor(out[i], c.xor(and_term, c.product(or_xor, diff[i])))
    lt_term = c.product(flags[ALU_LT], lt)
    out[0] = c.xor(out[0], c.xor(lt_term, c.product(flags[ALU_LTU], ltu)))
    offset = list(dt)
    for i in range(64):
        moved = c.product(flags[ALU_INDIRECT], c.xor(out[i], pc4[i]))
        out[i] = c.xor(out[i], moved)
        if i > 0:
            offset[i] = c.xor(offset[i], moved)

    taken = flags[ALU_ALWAYS]
    for bit, holds in zip(ALU_BRANCHES, (eq, ne, lt, c.invert(lt), ltu, c.invert(ltu))):
        taken = c.xor(taken, c.product(flags[bit], holds))
    for i, wire in enumerate(out):
        c.output(0, i, wire)
    for i, bit in enumerate(offset):
        c.and_output(1, i, taken, bit)
    return c


def _add(c: _GateList, x: Sequence[Wire], y: Sequence[Wire]) -> list[Wire]:
    """`x + y` over `len(x)` bits, the carry out of the top bit dropped: a ripple-carry adder, one product per bit but the top."""
    carry: Wire = None
    total: list[Wire] = []
    for i, (wx, wy) in enumerate(zip(x, y, strict=True)):
        xc, yc = c.xor(wx, carry), c.xor(wy, carry)
        total.append(c.xor(xc, wy))
        if i + 1 < len(x):
            carry = c.xor(c.product(xc, yc), carry)
    return total


def _shift_bytes(c: _GateList, x: Sequence[Wire], amount: Sequence[Wire], left: bool, bits: int) -> list[Wire]:
    """`x` shifted by `8 * amount` bits, `amount` being three bits. Only the low `bits` bits of the result are made, the
    ones the caller reads."""
    x = list(x)
    for stage, bit in enumerate(amount):
        by = 8 << stage
        moved = [x[i - by] if i >= by else None for i in range(64)] if left else [x[i + by] if i + by < 64 else None for i in range(64)]
        x = [c.mux(bit, moved[i], x[i]) for i in range(bits if stage + 1 == len(amount) else 64)]
    return x


def _bus_address(c: _GateList, v1: Sequence[Wire], imm: Sequence[Wire], log_width: Sequence[Wire]) -> tuple[list[Wire], list[Wire], list[Wire]]:
    """A load's or a store's address `v1 + imm`, the width's thresholds (at least 2 bytes, at least 4), and what goes
    on the memory bus: the address of the 64-bit cell, with the bits that misalign the access left in. A cell's
    address is a multiple of 8, so a misaligned access names no cell at all. A doubleword is LD's or SD's, so the two
    width bits are never both set (their OR is their XOR) and bit 2 never misaligns: it is cleared."""
    address = _add(c, v1, imm)
    thresholds = [c.xor(log_width[0], log_width[1]), log_width[1]]
    bus = [c.product(address[i], thresholds[i]) for i in range(2)] + [None] + address[3:]
    return address, thresholds, bus


def _load() -> _GateList:
    """(v1, imm, flags, cell) -> (address, out): the bytes of `cell` the address names, extended to 64 bits."""
    c = _GateList((64, 64, 3, 64), (64, 64))
    v1, imm, flags, cell = c.inputs
    address, (ge2, ge4), bus = _bus_address(c, v1, imm, flags[:2])
    # At most 4 bytes are loaded, so only the low half of the shifted cell is read.
    value = _shift_bytes(c, cell, address[:3], left=False, bits=32)
    # The extension: the value's top bit, which the width places, if the load is signed.
    sign: Wire = None
    for width, bit in ((c.invert(ge2), 7), (c.xor(ge2, ge4), 15), (ge4, 31)):
        sign = c.xor(sign, c.product(width, value[bit]))
    extension = c.product(flags[2], sign)
    for i, wire in enumerate(bus):
        c.output(0, i, wire)
    for i in range(64):
        c.output(1, i, value[i] if i < 8 else c.mux(ge2, value[i], extension) if i < 16 else c.mux(ge4, value[i], extension) if i < 32 else extension)
    return c


def _store() -> _GateList:
    """(v1, v2, imm, flags, cell) -> (address, new cell): `cell` with the bytes the address names replaced by the low
    bytes of `v2`."""
    c = _GateList((64, 64, 64, 2, 64), (64, 64))
    v1, v2, imm, flags, cell = c.inputs
    address, thresholds, bus = _bus_address(c, v1, imm, flags)
    # At most 4 bytes are stored, so the high half of v2 is never written.
    value = _shift_bytes(c, [*v2[:32], *[None] * 32], address[:3], left=True, bits=64)
    # Byte j is written when it shares the access's block: bit k of j equals bit k of the address wherever the
    # width does not already span both. No width spans bit 2, so there the byte's bit must equal the address's.
    spans = [[c.either(c.invert(address[k]), thresholds[k]), c.either(address[k], thresholds[k])] for k in range(2)]
    spans.append([c.invert(address[2]), address[2]])
    for i, wire in enumerate(bus):
        c.output(0, i, wire)
    for j in range(8):
        written = c.product(c.product(spans[0][j & 1], spans[1][j >> 1 & 1]), spans[2][j >> 2])
        for i in range(8 * j, 8 * j + 8):
            c.output(1, i, c.mux(written, value[i], cell[i]))
    return c


def _word_address() -> _GateList:
    """(v1, imm) -> address, the circuit of a doubleword load or store: the adder alone. A doubleword's misalignment
    bits are all three low ones, so the sum itself goes on the memory bus."""
    c = _GateList((64, 64), (64,))
    v1, imm = c.inputs
    for i, wire in enumerate(_add(c, v1, imm)):
        c.output(0, i, wire)
    return c


def _add_with_carry(c: _GateList, x: Sequence[Wire], y: Sequence[Wire], carry: Wire) -> tuple[list[Wire], Wire]:
    """`x + y + carry`, and the carry out of the top bit: one product per bit."""
    total: list[Wire] = []
    for wx, wy in zip(x, y, strict=True):
        xc, yc = c.xor(wx, carry), c.xor(wy, carry)
        total.append(c.xor(xc, wy))
        carry = c.xor(c.product(xc, yc), carry)
    return total, carry


def _sext32_if(c: _GateList, word: Wire, x: Sequence[Wire]) -> list[Wire]:
    """`x`, its bits from 32 up replaced by bit 31 when `word` is set."""
    return list(x[:32]) + [c.mux(word, x[31], bit) for bit in x[32:]]


def _shift() -> _GateList:
    """(v1, v2, imm, flags) -> out. One right shifter serves both directions, a left shift being a right shift of the
    reversed word. The flags: right, arithmetic (which comes with right), and the 32-bit form."""
    c = _GateList((64, 64, 64, 3), (64,))
    v1, v2, imm, (right, arith, word) = c.inputs
    # The amount: six bits, five for a word shift.
    amount = [c.xor(v2[i], imm[i]) for i in range(6)]
    amount[5] = c.product(c.invert(word), amount[5])
    # A word shift takes the low 32 bits, extended by the sign for an arithmetic one, by zero otherwise.
    low_sign = c.product(arith, v1[31])
    x = v1[:32] + [c.mux(word, low_sign, bit) for bit in v1[32:]]
    fill = c.product(arith, x[63])  # what a right shift brings in from the top
    y = [c.mux(right, x[i], x[63 - i]) for i in range(64)]
    for stage, bit in enumerate(amount):
        y = [c.mux(bit, y[i + (1 << stage)] if i + (1 << stage) < 64 else fill, y[i]) for i in range(64)]
    y = [c.mux(right, y[i], y[63 - i]) for i in range(64)]
    for i, wire in enumerate(_sext32_if(c, word, y)):
        c.output(0, i, wire)
    return c


def _multiply(c: _GateList, a: Sequence[Wire], b: Sequence[Wire], n: int) -> list[Wire]:
    """The low `n` bits of `a * b`. With `e_ij = not(a_i ^ b_j)`, `2 a_i b_j = a_i + b_j - 1 + e_ij`, so twice the product
    is a sum of 66 rows of affine bits: `(a_i ? b : not b) << i`, then `not a + a 2^64` and the same for `b`.
    Its column 0 is `2 + 2g` with `g = (not a_0)(not b_0)`, so after that one product the identity halves, `1` and `g`
    taking the empty low bits of two rows. Carry-save steps then compress three rows into two, the three ending
    lowest each time, and a ripple-carry addition finishes. Every product is a majority."""
    width = (1 << n) - 1
    not_a = [c.invert(wire) for wire in a]
    not_b = [c.invert(wire) for wire in b]
    g = c.product(not_a[0], not_b[0])

    rows: list[list[Wire]] = [[None] * n for _ in range(66)]
    for i in range(64):
        for j in range(64):
            if 0 <= i + j - 1 < n:
                rows[i][i + j - 1] = c.xor(b[j], not_a[i])
    for row, low, high in ((64, not_a, a), (65, not_b, b)):
        length = min(64, n - 63)
        rows[row][:63] = low[1:]
        rows[row][63 : 63 + length] = high[:length]
    rows[2][0], rows[3][0] = c.one, g
    if n == 128:
        rows[64][127] = c.one  # half of the constant 2^128, which survives only mod 2^128
    present = [sum(1 << p for p in range(n) if row[p] is not None) for row in rows]

    live = list(range(66))
    while len(live) > 2:
        # The three rows ending lowest: by highest position, then by lowest, ties in `live` order.
        order = sorted(range(len(live)), key=lambda t: (present[live[t]].bit_length(), (present[live[t]] & -present[live[t]]).bit_length()))
        x, y, z = (live[t] for t in order[:3])
        live = [row for row in live if row not in (x, y, z)] + [x, y]
        px, py, pz = present[x], present[y], present[z]
        pairs = ((px & py) | (px & pz) | (py & pz)) & (width >> 1)
        triples = px & py & pz
        products = moves = 0
        for p in range(n - 1):
            if (pairs >> p) & 1:
                # Where exactly two rows have a bit and the carry row is still free, one bit moves into it.
                if not (triples >> p) & 1 and not ((products << 1) >> p) & 1:
                    moves |= 1 << p
                else:
                    products |= 1 << p
        total: list[Wire] = [None] * n
        carry: list[Wire] = [None] * n
        for p in range(n):
            wx, wy, wz = rows[x][p], rows[y][p], rows[z][p]
            if (products >> p) & 1:
                xz, yz = c.xor(wx, wz), c.xor(wy, wz)
                carry[p + 1] = c.xor(c.product(xz, yz), wz)
                total[p] = c.xor(xz, wy)
            elif ((moves & pz) >> p) & 1:
                carry[p], total[p] = wz, c.xor(wx, wy)
            elif ((moves & ~pz) >> p) & 1:
                carry[p], total[p] = wy, wx
            else:
                total[p] = c.xor(c.xor(wx, wz), wy)
        rows[x], rows[y] = total, carry
        present[x], present[y] = px | py | pz, (products << 1) | moves

    # The last two rows, by a ripple-carry addition: a carry is one product wherever two of the three are present.
    out: list[Wire] = []
    chain: Wire = None
    for p, (wx, wy) in enumerate(zip(rows[live[0]], rows[live[1]], strict=True)):
        if p + 1 < n and sum(wire is not None for wire in (wx, wy, chain)) >= 2:
            xc, yc = c.xor(wx, chain), c.xor(wy, chain)
            chain = c.xor(c.product(xc, yc), chain)
            out.append(c.xor(xc, wy))
        else:
            out.append(c.xor(c.xor(wx, wy), chain))
            chain = None
    return out


def _mul() -> _GateList:
    """(v1, v2, flags) -> out: the low word of the product, its low 32 bits sign-extended for the 32-bit form."""
    c = _GateList((64, 64, 1), (64,))
    v1, v2, (word,) = c.inputs
    for i, wire in enumerate(_sext32_if(c, word, _multiply(c, v1, v2, 64))):
        c.output(0, i, wire)
    return c


def _mulh() -> _GateList:
    """(v1, v2, flags) -> out: the high word of the product, each operand signed or not. The unsigned product's high
    word, less `v2` if `v1` is signed and negative, less `v1` if `v2` is: a negative operand is its unsigned reading
    minus 2^64. And `high - other` is `high + not(other) + 1`."""
    c = _GateList((64, 64, 2), (64,))
    v1, v2, flags = c.inputs
    high = _multiply(c, v1, v2, 128)[64:]
    for signed, operand, other in ((flags[0], v1, v2), (flags[1], v2, v1)):
        negative = c.product(signed, operand[63])
        high, _ = _add_with_carry(c, high, [c.product(negative, c.invert(bit)) for bit in other], negative)
    for i, wire in enumerate(high):
        c.output(0, i, wire)
    return c


def _negate_if(c: _GateList, negative: Wire, x: Sequence[Wire]) -> list[Wire]:
    """`x` negated if `negative`: `(x ^ negative) + negative`."""
    return _add_with_carry(c, [c.xor(bit, negative) for bit in x], [None] * 64, negative)[0]


def _div() -> _GateList:
    """(v1, v2, flags, q, r) -> (out, bad). The quotient's and the remainder's magnitudes `q` and `r` are the prover's,
    and `bad` is set unless they are the ones: `|n| = q |d| + r` over the integers (the product's high word zero,
    the sum without a carry) and `r < |d|`. A row puts `bad` where its bytecode entry holds zero, so it is zero.
    Dividing by zero checks nothing and returns what the specification says, all ones or the dividend, and the one
    overflow, -2^63 / -1, is no special case on magnitudes. The flags: signed, remainder, 32-bit."""
    c = _GateList((64, 64, 3, 64, 64), (64, 1))
    v1, v2, (signed, rem, word), q, r = c.inputs

    def extend(x: Sequence[Wire]) -> list[Wire]:
        """A word form divides the low 32 bits, extended as the division is signed or not."""
        sign = c.product(signed, x[31])
        return list(x[:32]) + [c.mux(word, sign, bit) for bit in x[32:]]

    n, d = extend(v1), extend(v2)
    n_negative, d_negative = c.product(signed, n[63]), c.product(signed, d[63])
    n_abs, d_abs = _negate_if(c, n_negative, n), _negate_if(c, d_negative, d)

    product = _multiply(c, q, d_abs, 128)
    overflows = reduce(c.either, product[64:], None)
    total, carries = _add_with_carry(c, product[:64], r, None)
    differs = reduce(c.either, [c.xor(x, y) for x, y in zip(total, n_abs)], None)
    # `r - |d|` does not borrow, which is `r + not(|d|) + 1` carrying out, when `r >= |d|`.
    _, too_large = _add_with_carry(c, r, [c.invert(bit) for bit in d_abs], c.one)
    d_nonzero = reduce(c.either, d, None)
    bad = c.product(d_nonzero, reduce(c.either, (carries, differs, too_large), overflows))

    # The quotient is negative when the operands' signs differ, the remainder when the dividend is.
    q_signed, r_signed = _negate_if(c, c.xor(n_negative, d_negative), q), _negate_if(c, n_negative, r)
    out: list[Wire] = []
    for i in range(64):
        result = c.mux(rem, r_signed[i], q_signed[i])
        out.append(c.mux(d_nonzero, result, c.mux(rem, n[i], c.one)))
    for i, wire in enumerate(_sext32_if(c, word, out)):
        c.output(0, i, wire)
    c.output(1, 0, bad)
    return c


def _blake2s() -> _GateList:
    """(t, f0, h[4], m[8]) -> out[4]: the BLAKE2s compression on the 32-bit halves of the words. Every G is six 32-bit
    additions, its two three-operand ones chained, and nothing but the carries is a product."""
    c = _GateList((64, 32, *[64] * 12), (64,) * 4)
    t, f0 = c.inputs[0], c.inputs[1]
    halves = [list(word[32 * i : 32 * i + 32]) for word in c.inputs[2:] for i in range(2)]
    h, m = halves[:8], halves[8:]

    def literal(x: int) -> list[Wire]:
        return [c.one if x >> i & 1 else None for i in range(32)]

    def rotr(w: Sequence[Wire], r: int) -> list[Wire]:
        return [w[(i + r) % 32] for i in range(32)]

    def xor(x: Sequence[Wire], y: Sequence[Wire]) -> list[Wire]:
        return [c.xor(a, b) for a, b in zip(x, y, strict=True)]

    v = [list(word) for word in h] + [literal(x) for x in BLAKE2S_IV[:4]]
    v += [xor(literal(BLAKE2S_IV[4 + i]), x) for i, x in enumerate((t[:32], t[32:], f0, [None] * 32))]
    for sigma in BLAKE2S_SIGMA:
        for g, (a, b, cc, d) in enumerate(BLAKE2S_G_LANES):
            for x, r1, r2 in ((m[sigma[2 * g]], 16, 12), (m[sigma[2 * g + 1]], 8, 7)):
                v[a] = _add(c, _add(c, v[a], v[b]), x)
                v[d] = rotr(xor(v[d], v[a]), r1)
                v[cc] = _add(c, v[cc], v[d])
                v[b] = rotr(xor(v[b], v[cc]), r2)
    for i in range(8):
        for bit, wire in enumerate(xor(xor(h[i], v[i]), v[i + 8])):
            c.output(i // 2, 32 * (i % 2) + bit, wire)
    return c


def _clock(slots: Sequence[int], inputs: Sequence[int] = (), outputs: Sequence[int] = ()) -> _GateList:
    """(ts, prev_0, ..., prev_n) -> step, for a row whose accesses are in clock slots `slots`: the next clock is
    ts ^ step, ts one cycle on when the row is live (bit 40) and ts itself on a padding row. Bit 41 of step is set
    when an access is out of order: its previous timestamp disagrees with ts on the live bit, or, on a live row, is
    not strictly below ts ^ slot. Each input reads its bits up to the live bit, the others being forced zero, and ts
    has its slot bits forced zero too, so ts | slot, which the order check compares with, is ts ^ slot. Ports of the
    widths `inputs` and `outputs` follow its own, for a table with no class circuit to compute what it needs."""
    c = _GateList((range(SLOT_BITS, LIVE_BIT + 1), *(LIVE_BIT + 1,) * len(slots), *inputs), (FAIL_BIT + 1, *outputs))
    ts = c.inputs[0]
    live = ts[LIVE_BIT]
    in_order: list[Wire] = []
    disagree: Wire = None
    for i, slot in enumerate(slots):
        prev = c.inputs[1 + i]
        # prev < ts ^ slot exactly when (ts ^ slot) + not(prev) carries out of bit 39, the two agreeing on bit 40.
        carry: Wire = None
        for bit in range(LIVE_BIT):
            not_prev = c.invert(prev[bit])
            if bit >= SLOT_BITS:
                carry = c.xor(c.product(c.xor(ts[bit], carry), c.xor(not_prev, carry)), carry)
            elif slot >> bit & 1:
                carry = c.either(not_prev, carry)  # the slot's bits are constants, so the carry is an OR or an AND
            else:
                carry = c.product(not_prev, carry)
        in_order.append(carry)
        disagree = c.either(disagree, c.xor(prev[LIVE_BIT], live))
    late = c.product(live, c.invert(reduce(c.product, in_order)))
    fail = c.either(late, disagree)
    # The cycle count advances by `live`: bit j of step is the carry into bit j.
    carry = live
    c.output(0, SLOT_BITS, carry)
    for bit in range(SLOT_BITS, LIVE_BIT):
        carry = c.and_output(0, bit + 1, ts[bit], carry)
    c.output(0, FAIL_BIT, fail)
    return c


def _increment(c: _GateList, x: Sequence[Wire], bit: int) -> list[Wire]:
    """x + 2^bit modulo 2^64: the carry enters at `bit` and ripples up, one product per position past it, the carry
    into bit + 1 being x_bit itself."""
    out = list(x)
    carry = c.one
    for i in range(bit, 64):
        total = c.xor(out[i], carry)
        if i + 1 < 64:  # the carry out of the top position falls off the modulus
            carry = out[i] if i == bit else c.product(out[i], carry)
        out[i] = total
    return out


def _ext_clock(slots: Sequence[int]) -> _GateList:
    """(ts, prev_0, ..., prev_11, v1, v2, vd, flags) -> (step, accumulate, base, the addresses of limbs 1, 2, 4, 5, 7
    and 8): the clock circuit of the extension-field table, which also splits the flags into their two bits, each a
    whole port, and computes p + 8 and p + 16 for each pointer, a's, then b's, then c's, by incrementers. A base-field
    b's are gated off to zero, the register number of x0. A pointer off its word leaves its low bits in every limb's
    address, which then names no cell."""
    c = _clock(slots, (64, 64, 64, 2), (1, 1, *[64] * len(EXT_OFFSET_LIMBS)))
    *pointers, (accumulate_bit, base) = c.inputs[1 + len(slots) :]
    c.output(1, 0, accumulate_bit)
    c.output(2, 0, base)
    not_base = c.invert(base)
    for i, pointer in enumerate(pointers):
        for j, bit in enumerate((3, 4)):
            for k, wire in enumerate(_increment(c, pointer, bit)):
                if i == 1:
                    c.and_output(3 + 2 * i + j, k, not_base, wire)
                else:
                    c.output(3 + 2 * i + j, k, wire)
    return c


HASH_PORTS = ("v2", "flags", *(f"cell_{k}" for k in (*range(4), *range(8, 16))), *(f"cell_new_{HASH_OUT_WORD + j}" for j in range(4)))
HASH_FINAL = 2**32 - 1

TABLES = (
    Table("alu", 0, True, "none", _alu().circuit(), ("v1", "v2", "imm", "flags", "dt", "pc4", "out", "jump"), ALU_LEGAL_FLAGS),
    # A load's flags are log2 of its width in bytes, then whether it sign-extends; a store's, log2 of its width. A
    # doubleword is LD's or SD's, which have no flags: their circuit is the address alone, the word moved a column.
    Table("load", 1, False, "read", _load().circuit(), ("v1", "imm", "flags", "cell_0", "address", "out"), frozenset((0, 1, 2, 4, 5, 6))),
    Table("store", 2, False, "write", _store().circuit(), ("v1", "v2", "imm", "flags", "cell_0", "address", "cell_new_0"), frozenset(range(3))),
    Table("ld", 3, False, "read", _word_address().circuit(), ("v1", "imm", "address"), frozenset((0,)), copies=True),
    Table("sd", 4, False, "write", _word_address().circuit(), ("v1", "imm", "address"), frozenset((0,)), copies=True),
    # A shift's flags: right, arithmetic (with right), 32-bit. A product's: 32-bit; its high word's: which operands are signed.
    Table("shift", 5, False, "none", _shift().circuit(), ("v1", "v2", "imm", "flags", "out"), frozenset((0, 1, 3, 4, 5, 7))),
    Table("mul", 6, False, "none", _mul().circuit(), ("v1", "v2", "flags", "out"), frozenset((0, 1))),
    Table("mulh", 7, False, "none", _mulh().circuit(), ("v1", "v2", "flags", "out"), frozenset((0, 1, 3))),
    # A division's flags: signed, remainder, 32-bit. Its two hints are in its witness and in no column.
    Table("div", 8, False, "none", _div().circuit(), ("v1", "v2", "flags", None, None, "out", "bad"), frozenset(range(8))),
    # The BLAKE2s precompile: the counter is v2 and the flags are the finalization word, all ones on the last block.
    Table("hash", 9, False, "block", _blake2s().circuit(), HASH_PORTS, frozenset((0, HASH_FINAL))),
    # The extension-field precompile, with no class circuit: a at v1, b at v2 and c at the address in rd. Its identities
    # say the product; its clock circuit splits the flags (accumulate, base field) and computes the limbs' addresses.
    Table(
        "ext",
        10,
        False,
        "limbs",
        None,
        (),
        EXT_LEGAL_FLAGS,
        clock_inputs=("v1", "v2", "vd", "flags"),
        clock_outputs=EXT_CLOCK_OUTPUTS,
        clock_gates=_ext_clock,
    ),
)

TABLE_WIDTHS = tuple(t.width for t in TABLES)
# The packed flock witnesses: every class circuit, in table order (the tables that have one come first), then every
# table's clock circuit.
FLOCKS = (
    *((table, table.circuit, table.ports) for table in TABLES if table.circuit),
    *((table, table.clock, table.clock_ports) for table in TABLES),
)
WITNESS_COLUMNS = tuple(NUM_FRAMEWORK_COLUMNS + index for index in range(len(FLOCKS)))
GLOBAL_COLUMN_BASES = tuple(NUM_FRAMEWORK_COLUMNS + len(FLOCKS) + sum(TABLE_WIDTHS[:table]) for table in range(len(TABLES)))
# Each table's packed register numbers, one word per row, after every table's columns.
REGISTER_COLUMNS = tuple(GLOBAL_COLUMN_BASES[-1] + TABLE_WIDTHS[-1] + table for table in range(len(TABLES)))


def register_words(table_log_heights: Sequence[int]) -> list[list[int]]:
    """The committed register words, each the tables whose register numbers it packs, in table order: each table joins
    the first word of its height with room for its fields, or opens one, committed in its own register column. Tables
    of one height share their table-sumcheck point, so a word is one ring-switched claim."""
    words: list[list[int]] = []
    used: list[int] = []
    for table in TABLES:
        bits = sum(width for _, width in table.registers)
        height = table_log_heights[table.opcode]
        for index, word in enumerate(words):
            if table_log_heights[word[0]] == height and used[index] + bits <= K_BITS:
                word.append(table.opcode)
                used[index] += bits
                break
        else:
            words.append([table.opcode])
            used.append(bits)
    return words


def check_bytecode(bytecode: Sequence[K]) -> None:
    """The proof system is sound for any decoded table, so what makes one RISC-V is checked here: an entry some table
    can read names two registers to read and a cell other than x0 to write, its successor is pc + 4, its flags are
    ones its class defines, and only a branch or a jal has a jump offset, a jal linking pc + 4 as a constant added to
    x0. An entry with no tag can be read by no table: a run reaching one has no proof. It has one form, the illegal
    entry's, and the halt slot is one."""
    size = len(bytecode) // 2**BUS_BITS
    fields = [[int(word) for word in bytecode[slot * size : (slot + 1) * size]] for slot in range(2**BUS_BITS)]
    tag, flags, a1, a2, ad, imm, pc4, dt = fields[BYTECODE_PUBLIC_SLOT:BAD_SLOT]
    exit = fields[EXIT_SLOT]
    outside = fields[:BYTECODE_PUBLIC_SLOT] + [fields[BAD_SLOT]] + fields[EXIT_SLOT + 1 :]
    require(not any(any(column) for column in outside), "a bytecode slot outside an entry's fields is nonzero")
    tags = {int(_gpow(table.opcode)): table for table in TABLES}
    require(size > 0 and tag[-1] == 0, "the halt slot is not an illegal entry")
    for z in range(size):
        if tag[z] == 0:
            illegal = flags[z] == a1[z] == a2[z] == imm[z] == dt[z] == exit[z] == 0 and ad[z] == SINK
            require(illegal and pc4[z] == TEXT_BASE + 4 * z + 4, "an illegal entry is not in its one form")
            continue
        table = tags.get(tag[z])
        if table is None:
            raise VerificationError("a bytecode entry names no class")
        require(a1[z] < 32 and a2[z] < 32 and 1 <= ad[z] <= SINK, "a bytecode entry misnames a register")
        require(pc4[z] == TEXT_BASE + 4 * z + 4, "a bytecode entry's successor is not pc + 4")
        require(flags[z] in table.legal_flags, "a bytecode entry's flags are not its class's")
        require(exit[z] <= 1, "an exit selector is not a bit")
        if exit[z]:
            halt_pc = TEXT_BASE + 4 * (size - 1)
            require(
                table.control and flags[z] == 1 << ALU_ALWAYS and a1[z] == a2[z] == imm[z] == 0 and ad[z] == SINK and dt[z] == (halt_pc ^ pc4[z]),
                "an exit entry is not ECALL",
            )
        elif table.control and flags[z] == 1 << ALU_ALWAYS:
            require(a1[z] == a2[z] == 0 and imm[z] == pc4[z], "a bytecode entry has invalid control flow")
        elif not (table.control and any(flags[z] & (1 << bit) for bit in ALU_BRANCHES)):
            require(dt[z] == 0, "a bytecode entry has invalid control flow")
        # A field the class's table holds at a constant has to be that constant.
        require(table.reads_rs2 or a2[z] == 0, "a bytecode entry reads an rs2 its class does not")
        require(table.writes_rd or table.reads_rd or ad[z] == SINK, "a bytecode entry writes an rd its class does not")
        require(not table.reads_rd or ad[z] < SINK, "a bytecode entry reads an address from the sink")
        require("imm" in table.words or imm[z] == 0, "a bytecode entry has an immediate its class does not")


def build_layout(
    bytecode: Sequence[K],
    entry_pc: int,
    log_ram: int,
    log_advice: int,
    ram: Sequence[tuple[int, Sequence[int]]],
    table_log_heights: Sequence[int],
    final_clock: E,
) -> Layout:
    log_bytecode = log2_strict(len(bytecode)) - BUS_BITS
    require(
        all(table.min_log_height <= log_height <= MAX_LOG_ROWS for table, log_height in zip(TABLES, table_log_heights, strict=True))
        and 0 <= log_bytecode <= MAX_LOG_TEXT,
        "invalid announced table sizes",
    )
    require(
        log_ram <= MAX_LOG_RAM and all(offset + len(words) <= 2**log_ram for offset, words in ram),
        "RAM does not hold its image",
    )
    require(0 <= log_advice <= MAX_LOG_ADVICE, "the advice exceeds its region")

    push: list[BusBlock] = []
    pull: list[BusBlock] = []
    for table, height in zip(TABLES, table_log_heights, strict=True):
        flushes = table.flushes
        for coordinates in flushes.push:
            push.append(BusBlock(height, coordinates, table.opcode))
        for coordinates in flushes.pull:
            pull.append(BusBlock(height, coordinates, table.opcode))
    # The lookup array's table side, pushing an entry as often as it is read. The bus reads enough of a multiplicity's
    # bits for every read these tables can make: each row reads the bytecode once.
    log_rows = framework_log_rows(log_bytecode, log_ram, log_advice)
    reads = {"bytecode": sum(2**height for height in table_log_heights)}
    producers = tuple(Producer(log_rows[lookup], SHARED[f"{lookup}_mult"], reads[lookup].bit_length()) for lookup in LOOKUPS)

    # Every column's log size, in global order: the framework's, the flock witnesses', then each table's block.
    witness_kappas = [table_log_heights[table.opcode] + slot_bits(circuit) for table, circuit, _ in FLOCKS]
    kappas = [*(log_rows[block] for _, block in SHARED_COLUMNS), *witness_kappas]
    for table in TABLES:
        kappas += [table_log_heights[table.opcode]] * table.width
    kappas += [table_log_heights[table.opcode] for table in TABLES]
    hosts = {REGISTER_COLUMNS[word[0]] for word in register_words(table_log_heights)}

    # A circuit word gets no block of its own: it is committed inside its circuit's flock witness, whose ports
    # interleave, so it sits at that witness's offset behind its own port's bits. Same width either way.
    words = {
        GLOBAL_COLUMN_BASES[table.opcode] + _cols(table.columns, name)[0]: (witness, port, slot_bits(circuit))
        for witness, (table, circuit, ports) in enumerate(FLOCKS)
        for port, name in enumerate(ports)
        if name
    }
    # A register number is no column of the stack either: it is a field of a register word, and so is the register
    # column of a table whose numbers an earlier table's word holds.
    sliced = {GLOBAL_COLUMN_BASES[table.opcode] + local for table in TABLES for local, _ in table.registers}
    sliced |= set(REGISTER_COLUMNS) - hosts
    blocks = {column: kappa for column, kappa in enumerate(kappas) if column not in words and column not in sliced}
    block_offsets, placed = stack_offsets(list(blocks.values()))
    offsets = dict(zip(blocks, block_offsets))
    stack_log = max(MIN_STACKED_LOG, log2_ceil(placed))  # Floor at the PCS minimum
    # The columns tile from 0, so only the lanes up to the last placed word are committed.
    stack_lanes = max(1, -(-placed // 2 ** (stack_log - INITIAL_FOLDING_FACTOR)))

    def placement(column: int, kappa: int) -> Placement:
        if column not in words:
            return Placement(kappa, offsets[column])
        witness, port, bits = words[column]
        return Placement(kappa, offsets[WITNESS_COLUMNS[witness]] + port, bits)

    placements = {column: placement(column, kappa) for column, kappa in enumerate(kappas) if column not in sliced}
    return Layout(
        log_bytecode,
        bytecode,
        entry_pc,
        log_ram,
        log_advice,
        ram,
        tuple(push),
        tuple(pull),
        producers,
        placements,
        stack_log,
        stack_lanes,
        tuple(table_log_heights),
        final_clock,
    )


def verify_flock(circuits: Sequence[tuple[FlockCircuit, int]], transcript: Transcript) -> list[tuple[MultilinearPoint, tuple[E, ...], MatrixForm, E]]:
    """The reductions of every circuit, each over 2^log_height instances, in protocol order: the batched zerocheck,
    then the batched lincheck. What they leave, per circuit, is the point and the 64 claims s[i] = z(i, point), i < 64,
    for ring switching to bind, and the matrix form with the value it must take."""
    zerochecks = verify_flock_zerocheck([circuit.log_size + log_height for circuit, log_height in circuits], transcript)
    return verify_flock_lincheck([circuit for circuit, _ in circuits], zerochecks, transcript)


# Ring switching --------------------------------------------------------------

# The Frobenius shifts of the six stages composing Phi, one challenge each.
RING_MAP_SHIFTS = (32, 16, 8, 4, 2, 1)


def _phi(value: E, challenges: Sequence[E]) -> E:
    """The drawn map, stage by stage: `a_p+1 = a_p + f_p a_p^(2^shift)`."""
    for challenge, shift in zip(challenges, RING_MAP_SHIFTS, strict=True):
        value += challenge * value ** (2**shift)
    return value


def _ring_weight(r: MultilinearPoint, scale: E, r_prime: Sequence[E], coefficients: Sequence[E]) -> E:
    """The weight `W(u) = Phi(scale eq(r, u))`, extended and evaluated by the opening at
    `r_prime`: `sum_k c_k scale^(2^k) prod_n (1 + r_n^(2^k) + r'_n)`."""
    total = ZERO
    frobenius = list(r)
    for c in coefficients:
        product = c * scale
        for value, challenge in zip(frobenius, r_prime, strict=True):
            product *= ONE + value + challenge
        total += product
        frobenius = [value**2 for value in frobenius]
        scale = scale.square()
    return total


def ring_switch(claims: Sequence[tuple[Placement, MultilinearPoint, Sequence[E]]], transcript: Transcript) -> StackClaim:
    """Every ring-switched claim, 64 values s[i] = q(i, point) on its region of the stack, becomes part of one dense
    claim `sum_u W(u) q(u) = target` on the stack.

    Once every claim is fixed, draw gamma_rs: claim j takes the scale gamma_rs^j, and the family's 64 slices are the
    claims' slices so weighted. Then draw Phi, take the target `T = sum_i x^i Phi(family_i)` once, and the weight that
    puts `Phi(gamma_rs^j eq(point_j, u))` on claim j's region. The points need not be related."""
    scales = powers(transcript.sample(), len(claims))
    family = [E.sum(scale * s[i] for scale, (_, _, s) in zip(scales, claims, strict=True)) for i in range(K_BITS)]
    challenges = transcript.samples(len(RING_MAP_SHIFTS))
    # The same map as a Frobenius sum, `Phi(a) = sum_k c_k a^(2^k)` for k < 64.
    coefficients = [reduce(mul, (f ** (2 ** (k % s)) for f, s in zip(challenges, RING_MAP_SHIFTS) if k & s), ONE) for k in range(K_BITS)]
    target = poly_eval([_phi(value, challenges) for value in family], GEN)

    def weight(x: Sequence[E]) -> E:
        # Each claim is supported on its witness's region of the stack, so its weight carries the placement's selector.
        return E.sum(
            region.eq_above(x) * _ring_weight(point, scale, x[: region.variables], coefficients)
            for scale, (region, point, _) in zip(scales, claims, strict=True)
        )

    return (weight, target)


# Stacked opening -------------------------------------------------------------


type StackClaim = tuple[Callable[[Sequence[E]], E], E]  # the weight it puts on the stack, and the value it claims for it


def verify_stacked_opening(
    transcript: Transcript, root: Digest, stack_log: int, stack_lanes: int, log_inv_rate: int, claims: Sequence[StackClaim]
) -> None:
    """Discharge every claim on the committed stack in one opening: the same powers of one challenge
    batch the values into the target, and the weights into the basis WHIR evaluates at its terminal point.
    """
    weights, values = zip(*claims, strict=True)
    scales = powers(transcript.sample(), len(claims))
    verify_whir(
        transcript, stack_log, stack_lanes, log_inv_rate, dot(scales, values), root, lambda point: dot(scales, [weight(point) for weight in weights])
    )


def _bytecode_affine(producer: Producer, weights: Sequence[E], beta: E) -> Callable[[MultilinearPoint], list[E]]:
    """The bytecode's public columns P'_i = (beta + pi_alpha(entry x))^(2^i) - 1 at a point, short of the program's
    columns. Squaring is additive, so the separator and the address column TEXT_BASE + 4x are raised term by term, the
    address staying affine in the bits; the program's columns' share is the program's deferred claim."""

    def public(point: MultilinearPoint) -> list[E]:
        constant, weight = beta + weights[0] * SEP_BYTECODE + weights[1] * E(TEXT_BASE), weights[1]
        monomials = [E(1 << (bit + 2)) for bit in range(len(point))]
        values = []
        for _ in range(producer.bits):
            values.append(constant + weight * dot(point, monomials) + ONE)
            constant, weight = constant.square(), weight.square()
            monomials = [m.square() for m in monomials]
        return values

    return public


# Deferred claims ------------------------------------------------------------
#
# What the verifier leaves to the polynomials only the program or the VM's circuits fix: the table sumcheck's terminal
# identity short of the bytecode producer's program columns and of RAM's image, and each circuit's lincheck terminal
# identity short of its matrix form. Their points are challenges and stream scalars, and nothing is absorbed after them,
# so they can be settled after the rest of the proof, or by someone else.


@dataclass(frozen=True)
class ProgramPoint:
    """The program's polynomials at a point, whose value is

        sum_i twist[i] sum_x eq(chi, x) T(x, alpha)^(2^i) + image_weight image(image_point),

    T(x, alpha) = sum_s eq(alpha, s) T(x, s) the stacked bytecode table at entry x, and image RAM's image then zeros.
    The first sum is the producer's program columns, bit i's raised to 2^i: the Frobenius twist phi^i of the table at
    (phi^-i(chi), alpha), all bits' taken at once."""

    bytecode: MultilinearPoint  # chi, then alpha
    twist: tuple[E, ...]
    image_weight: E
    image_point: MultilinearPoint

    def evaluate(self, bytecode: Sequence[K], image: Sequence[int]) -> E:
        size = len(bytecode) >> BUS_BITS
        chi, alphas = self.bytecode[: log2_strict(size)], self.bytecode[log2_strict(size) :]
        weights = eq_kernel(alphas)
        slots = range(BYTECODE_PUBLIC_SLOT, EXIT_SLOT + 1)
        sums = [E.sum(weights[slot] * word for slot in slots if (word := bytecode[slot * size + x])) for x in range(size)]
        eq = eq_kernel(chi)
        total = ZERO
        for weight in self.twist:
            total += weight * dot(eq, sums)
            sums = [s.square() for s in sums]
        return total + self.image_weight * sparse_mle(((0, image),), self.image_point)


@dataclass(frozen=True)
class DeferredClaims:
    program: tuple[ProgramPoint, E]  # the point, and the value the program's polynomials must take there
    circuits: tuple[tuple[MatrixForm, E], ...]  # per circuit, in FLOCKS order, its matrix form and the value it must take

    def render(self) -> str:
        """One line per field, every element as its three limbs in hexadecimal, high first: what the Rust side renders
        for the same claims."""

        def line(name: str, values: Sequence[E]) -> str:
            return " ".join([name, *(f"{int(v.c2):016x}{int(v.c1):016x}{int(v.c0):016x}" for v in values)])

        point, value = self.program
        lines = [
            line("program value", [value]),
            line("program bytecode", point.bytecode),
            line("program twist", point.twist),
            line("program image_weight", [point.image_weight]),
            line("program image_point", point.image_point),
        ]
        for f, (form, value) in enumerate(self.circuits):
            lines += [
                line(f"circuit {f} value", [value]),
                line(f"circuit {f} alpha", [form.alpha]),
                line(f"circuit {f} row", [form.z_skip, *form.chi_in]),
                line(f"circuit {f} column", form.chi_in_prime),
                line(f"circuit {f} slices", form.s),
            ]
        return "\n".join(lines)


def verify_core(
    bytecode: Sequence[K],
    entry_pc: int,
    log_ram: int,
    log_advice: int,
    image: Sequence[int],
    output: Sequence[int],
    proof: Proof,
) -> DeferredClaims:
    """The statement: the program whose decoded table is `bytecode`, started at `entry_pc` on a RAM of `2^log_ram` words
    holding `image` then zeros, with an advice region of `2^log_advice` words holding whatever the prover put there,
    halts on `exit` with a0..a3 holding `output`. Everything but the deferred claims, which it returns."""
    require(len(output) == 4, "the output is four words")
    check_bytecode(bytecode)
    # Everything public and fixed is one digest, which seeds the transcript; every variable-length part is length-framed.
    halt_pc = TEXT_BASE + 4 * (len(bytecode) // 2**BUS_BITS - 1)
    require(entry_pc % 4 == 0 and TEXT_BASE <= entry_pc < halt_pc, "the entry pc is not an instruction of the text")
    preimage = b"leanvm-rv64im-11" + pack("<Q", len(bytecode)) + b"".join(word.to_bytes() for word in bytecode)
    preimage += pack("<5Q", entry_pc, halt_pc, log_ram, log_advice, len(image)) + pack(f"<{len(image)}Q", *image)
    transcript = Transcript(proof, blake2s_hash(preimage), [K(word) for word in output])

    # 1] table log-sizes, log-inv-rate in WHIR, and the clock the run ended on (a K element)
    announced = transcript.next_scalars(2 + len(TABLES))
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced value has a nonzero high limb")
    final_clock = int(announced[-1].c0)
    require(final_clock >> LIVE_BIT == 1 and final_clock % CYCLE == 0, "the final clock is not a live clock")
    table_logs = tuple(int(value.c0) for value in announced[: len(TABLES)])
    log_inverse_rate = int(announced[-2].c0)
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    ram = ((0, image),)
    layout = build_layout(bytecode, entry_pc, log_ram, log_advice, ram, table_logs, announced[-1])
    require(MIN_STACKED_LOG <= layout.stack_log <= MAX_STACKED_LOG, "committed size outside the PCS window")

    # 2] parse WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    root = Digest.from_halves(*transcript.next_scalars(2))

    # 3] Bus: one batched GKR over the push and pull trees, then the leaf decomposition, which leaves each table a
    # linear form per side and each producer a weight on each of its bits.
    bus = verify_bus_balance(layout, transcript)

    # 4] A table with a class circuit settles at the bus point: its columns there, short of its register numbers,
    # which the opening checks, are its forms' share of each side short of the numbers' part, which leaves the rest owed
    # (in characteristic two, the sum). Its register numbers are folded by the table sumcheck, at the other words' point.
    totals = list(bus.totals)
    claims = list(bus.claims)
    for table in TABLES:
        if table.circuit is None:
            continue
        sent = iter(transcript.next_scalars(table.width - len(table.registers)))
        numbers = {local for local, _ in table.registers}
        evaluations = tuple(ZERO if local in numbers else next(sent) for local in range(table.width))
        for side, form in enumerate(bus.forms[table.opcode]):
            totals[side] += form.evaluate(evaluations.__getitem__)
        claims.extend(table.column_claims(tuple(bus.point[: layout.table_log_heights[table.opcode]]), evaluations))

    # 5] One batched (back-loaded) "table sumcheck" over the tables and the producer, at the bus point, proving the
    # target what is left owed: the tables' bus forms (a settled table's on its register numbers alone) and the
    # producer's bits, weighted by the same powers of xi.
    # RAM's image is not in the target, nor the program's columns in the producer's public ones: their share of the
    # terminal identity is the program's deferred claim, the image's reaching it through every round's challenge.
    # A table's own identities take the next powers of xi, in table order, which no other form uses: their sums are
    # zero, so the target is the same, and matching it pins each of them to zero.
    xi = transcript.sample()
    form_powers = powers(xi, 2)  # one power per bus side, shared by every table
    identity_powers, start = [], len(form_powers)
    for table in TABLES:
        identity_powers.append(powers(xi, start + len(table.identities))[start:])
        start += len(table.identities)
    target = dot(form_powers, totals)
    (bytecode_producer,) = layout.producers
    publics = (_bytecode_affine(bytecode_producer, bus.weights, bus.beta),)
    producer_airs = [
        ProducerAir(producer.log_rows, tuple(form_powers[0] * c for c in coefficients), public)
        for producer, coefficients, public in zip(layout.producers, bus.producers, publics, strict=True)
    ]
    forms = [bus.forms[table.opcode] for table in TABLES]
    tables = table_sumcheck(layout.table_log_heights, forms, producer_airs, form_powers, identity_powers, bus.point, target, transcript)
    ((chi, _),), (twist,) = tables.families, tables.twists
    image_weight, image_point = bus.image
    program = ProgramPoint((*chi, *bus.alphas), twist, tables.target_weight * form_powers[0] * image_weight, image_point)
    claims.extend(tables.claims)

    # 6] the exit: a7 holds `exit` and a0..a3 the output when the run ends. A register's final value is the final
    # registers' column at the Boolean point naming it, a claim the verifier computes rather than receives.
    for register, value in ((SYSCALL_REGISTER, SYS_EXIT), *zip(OUTPUT_REGISTERS, output)):
        point = tuple(ONE if register >> bit & 1 else ZERO for bit in range(LOG_REGISTERS))
        claims.append(ColumnClaim(SHARED["register_final"], point, E(value)))

    # 7] every circuit via Flock, every class circuit then every table's clock circuit, each over its own packed
    # witness, batched under shared challenges, each leaving its matrix form to its circuit
    flocks = verify_flock([(circuit, layout.table_log_heights[table.opcode]) for table, circuit, _ in FLOCKS], transcript)
    families = [(point, s) for point, s, _, _ in flocks]
    # and the producer's bits, the 64 bit slices of its multiplicity column: the bits the bus reads, then zeros; and
    # each register word's, its tables' register numbers' bits at their shared point, then zeros, which an honest
    # word's unused bits are
    words = register_words(layout.table_log_heights)
    packed = [(tables.registers[word[0]][0], tuple(bit for t in word for bit in tables.registers[t][1])) for word in words]
    families += [(point, (*values, *[ZERO] * (K_BITS - len(values)))) for point, values in (*tables.families, *packed)]

    # 8] Ring-switching: one family for every claim, which leads the batch, taking the first power (lambda^0 = 1).
    columns = (*WITNESS_COLUMNS, *(producer.column for producer in layout.producers), *(REGISTER_COLUMNS[word[0]] for word in words))
    regions = [layout.placements[column] for column in columns]
    ring_claims = [(region, point, s) for region, (point, s) in zip(regions, families, strict=True)]
    verify_stacked_opening(
        transcript,
        root,
        layout.stack_log,
        layout.stack_lanes,
        log_inverse_rate,
        [ring_switch(ring_claims, transcript), *(c.on_stack(layout) for c in claims)],
    )
    transcript.finish()
    return DeferredClaims((program, tables.residual), tuple((form, value) for _, _, form, value in flocks))


def check_deferred(claims: DeferredClaims, bytecode: Sequence[K], image: Sequence[int]) -> None:
    """Evaluate the claims `verify_core` left: on the program's bytecode table and RAM image, and on each circuit's matrices."""
    point, value = claims.program
    require(point.evaluate(bytecode, image) == value, "table sumcheck terminal mismatch")
    for (_, circuit, _), (form, value) in zip(FLOCKS, claims.circuits, strict=True):
        require(form.evaluate(circuit) == value, "Flock lincheck terminal mismatch")


def verify_execution(
    bytecode: Sequence[K],
    entry_pc: int,
    log_ram: int,
    log_advice: int,
    image: Sequence[int],
    output: Sequence[int],
    proof: Proof,
) -> DeferredClaims:
    """`verify_core`, then `check_deferred`; returns the claims it checked."""
    claims = verify_core(bytecode, entry_pc, log_ram, log_advice, image, output, proof)
    check_deferred(claims, bytecode, image)
    return claims


def protocol_constants() -> str:
    """Every constant this verifier shares with the Rust one, as sorted `name value` lines. The two are written out
    twice on purpose, so something has to hold them together: `leanvm_core`'s `constants_match_the_python_verifier`
    renders the same lines from its own side and diffs them. Lists are comma-separated."""
    scalars = {
        "ADVICE_BASE": ADVICE_BASE,
        "BAD_SLOT": BAD_SLOT,
        "BUS_BITS": BUS_BITS,
        "EXIT_SLOT": EXIT_SLOT,
        "FAIL_BIT": FAIL_BIT,
        "CLOCK_START": CLOCK_START,
        "FLOCK_K_SKIP": FLOCK_K_SKIP,
        "FLOCK_MIN_LOG_SIZE": FLOCK_MIN_LOG_SIZE,
        "HASH_OUT_WORD": HASH_OUT_WORD,
        "HASH_WORDS": HASH_WORDS,
        "INITIAL_FOLDING_FACTOR": INITIAL_FOLDING_FACTOR,
        "LOG_PACKING": LOG_PACKING,
        "LIVE_BIT": LIVE_BIT,
        "LOG_REGISTERS": LOG_REGISTERS,
        "MAX_LOG_ADVICE": MAX_LOG_ADVICE,
        "MAX_LOG_RAM": MAX_LOG_RAM,
        "MAX_LOG_ROWS": MAX_LOG_ROWS,
        "MAX_LOG_TEXT": MAX_LOG_TEXT,
        "MAX_STACKED_LOG": MAX_STACKED_LOG,
        "MIN_STACKED_LOG": MIN_STACKED_LOG,
        "NUM_FRAMEWORK_COLUMNS": NUM_FRAMEWORK_COLUMNS,
        "QUERY_GRINDING_BITS": QUERY_GRINDING_BITS,
        "RAM_BASE": RAM_BASE,
        "RAM_SLOT": RAM_SLOT,
        "REGISTER_BITS": REGISTER_BITS,
        "RESIDUAL_MAX_LOG": RESIDUAL_MAX_LOG,
        "RS_DOMAIN_INITIAL_REDUCTION_FACTOR": RS_DOMAIN_INITIAL_REDUCTION_FACTOR,
        "RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR": RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR,
        "SEED_CLOCK": SEED_CLOCK,
        "SINK": SINK,
        "SLOT_BITS": SLOT_BITS,
        "SUBSEQUENT_FOLDING_FACTOR": SUBSEQUENT_FOLDING_FACTOR,
        "SYSCALL_REGISTER": SYSCALL_REGISTER,
        "SYS_EXIT": SYS_EXIT,
        "TEXT_BASE": TEXT_BASE,
        "UNGROUND_LOG_BYTECODE": UNGROUND_LOG_BYTECODE,
    }
    lines = [f"{name} {value}" for name, value in scalars.items()]
    lines.append("OUTPUT_REGISTERS " + ",".join(str(r) for r in OUTPUT_REGISTERS))
    lines.append("REGISTER_SLOTS " + ",".join(str(s) for s in REGISTER_SLOTS))
    for table in TABLES:
        prefix = f"TABLE.{table.name}"
        lines.append(f"{prefix}.opcode {table.opcode}")
        if table.circuit:  # a table with no class circuit has no class block either
            lines.append(f"{prefix}.k_log {table.circuit.log_size}")
            lines.append(f"{prefix}.const_pos {table.circuit.constant_column}")
            lines.append(f"{prefix}.slot_bits {slot_bits(table.circuit)}")
        lines.append(f"{prefix}.clock_k_log {table.clock.log_size}")
        lines.append(f"{prefix}.clock_const_pos {table.clock.constant_column}")
        lines.append(f"{prefix}.clock_ports {len(table.clock_ports)}")
        lines.append(f"{prefix}.min_log_height {table.min_log_height}")
        lines.append(f"{prefix}.ports {len(table.ports)}")
        lines.append(f"{prefix}.width {table.width}")
        lines.append(f"{prefix}.slots " + ",".join(str(s) for s in table.slots))
        lines.append(f"{prefix}.legal_flags " + ",".join(str(f) for f in sorted(table.legal_flags)))
    return "\n".join(sorted(lines))


def main(argv: Sequence[str] | None = None) -> int:
    import argparse

    if list(argv if argv is not None else sys.argv[1:]) == ["--constants"]:
        print(protocol_constants())
        return 0

    parser = argparse.ArgumentParser(description="Verify a leanVM execution proof")
    parser.add_argument("bytecode", type=Path, help="stacked bytecode multilinear, little-endian 64-bit words")
    parser.add_argument(
        "public",
        type=Path,
        help="little-endian 64-bit words: the entry pc, log2 of RAM's words, log2 of the advice's, the program's image (its length, then its words), the four output words",
    )
    parser.add_argument("stream", type=Path, help="the proof's scalar stream, 24-byte little-endian field elements")
    parser.add_argument("merkle_openings", type=Path, help="every Merkle opening: its leaf's words, then its sibling digests")
    parser.add_argument("--deferred", action="store_true", help="print the deferred claims before the verdict, one field a line")
    arguments = parser.parse_args(argv)
    try:
        encoded_bytecode = arguments.bytecode.read_bytes()
        require(len(encoded_bytecode) % 8 == 0, "bytecode is not a whole number of 64-bit words")
        bytecode = [K(int.from_bytes(encoded_bytecode[i : i + 8], "little")) for i in range(0, len(encoded_bytecode), 8)]
        encoded_public = arguments.public.read_bytes()
        require(len(encoded_public) % 8 == 0 and len(encoded_public) >= 8 * 8, "the public words are malformed")
        entry_pc, log_ram, log_advice, image_length, *rest = unpack(f"<{len(encoded_public) // 8}Q", encoded_public)
        require(len(rest) == image_length + 4, "the public words are malformed")
        image, output = rest[:image_length], rest[image_length:]
        proof = Proof.load(arguments.stream, arguments.merkle_openings)
        claims = verify_execution(bytecode, entry_pc, log_ram, log_advice, image, output, proof)
    except (OSError, ValueError, KeyError, VerificationError) as exc:
        parser.exit(1, f"verification failed: {exc}\n")
    if arguments.deferred:
        print(claims.render())
    print("verification succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
