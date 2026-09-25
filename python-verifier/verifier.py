from __future__ import annotations

import hashlib
import sys
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


def powers_mle(first: E, ratio: E, point: MultilinearPoint) -> E:
    """MLE of ``[first * ratio^z]`` at an LSB-first point. No such column is ever committed: this is its evaluation."""
    result = first
    ratio_power = ratio
    for challenge in point:
        result *= ONE + challenge * (ONE + ratio_power)
        ratio_power **= 2
    return result


def index_mle(point: MultilinearPoint) -> E:
    """MLE of ``[1, g, g^2, ...]`` at an LSB-first point."""
    return powers_mle(ONE, GEN, point)


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
    """One block of a bus side, always owned by a table. The five blocks no table owns are the framework, on `BusLayout`."""

    log_rows: int  # the owner's height: this block flushes 2^log_rows rows
    coordinates: tuple[Form, ...]  # the tuple flushed, over the owner's OWN local column indices; stays symbolic until its table sumcheck
    owner: int  # whose block it is, by opcode


@dataclass(frozen=True)
class BusLayout:
    """Where a side's blocks sit in the stacked leaf cube. Split by kind because framework coordinates are
    public, so the verifier evaluates their fingerprints outright, while a table's stay symbolic until its sumcheck."""

    depth: int  # log2 of the padded cube, so how many layers the side's GKR walks
    framework: tuple[
        Placement, ...
    ]  # the blocks no table owns, stacked first: boundary state, memory, bytecode, the two range arrays (none on the count side)
    tables: tuple[Placement, ...]  # one per block a table owns, in the side's own block order


FrameworkLogRows = tuple[int, int, int, int, int] | tuple[()]  # state, memory, bytecode, range low, range high


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
    # state, registers, RAM, the advice, bytecode, the two range arrays
    framework_log_rows = (0, LOG_REGISTERS, layout.log_ram, layout.log_advice, layout.log_bytecode, RANGE_LOG, RANGE_LOG)
    push_layout = bus_layout(framework_log_rows, layout.push)
    pull_layout = bus_layout(framework_log_rows, layout.pull)
    count_layout = bus_layout((), layout.count)

    alphas = transcript.samples(BUS_BITS)
    weights = eq_kernel(alphas)
    beta = transcript.sample()
    count_root, point, tree_values = verify_gkr_grand_products(push_layout.depth, transcript)
    require(count_root != ZERO, "a bus count is zero")

    # The framework blocks' committed columns, in the order the two sides first name them. The push side names the
    # advice's initial words, every other seed being public (the registers start at zero, RAM at the input and the
    # program's image); the pull side names each read-write array's final timestamps and values, then each read-only
    # array's final counts.
    register_low = tuple(point[:LOG_REGISTERS])
    ram_low = tuple(point[: layout.log_ram])
    advice_low = tuple(point[: layout.log_advice])
    bytecode_low = tuple(point[: layout.log_bytecode])
    range_low = tuple(point[:RANGE_LOG])
    advice_initial = transcript.next_scalar()
    register_final_ts = transcript.next_scalar()
    register_final = transcript.next_scalar()
    ram_final_ts = transcript.next_scalar()
    ram_final = transcript.next_scalar()
    advice_final_ts = transcript.next_scalar()
    advice_final = transcript.next_scalar()
    bytecode_final = transcript.next_scalar()
    range_lo_final = transcript.next_scalar()
    range_hi_final = transcript.next_scalar()
    claims = [
        ColumnClaim(ADVICE_INITIAL, advice_low, advice_initial),
        ColumnClaim(REGISTER_FINAL_TIMESTAMPS, register_low, register_final_ts),
        ColumnClaim(REGISTER_FINAL, register_low, register_final),
        ColumnClaim(RAM_FINAL_TIMESTAMPS, ram_low, ram_final_ts),
        ColumnClaim(RAM_FINAL, ram_low, ram_final),
        ColumnClaim(ADVICE_FINAL_TIMESTAMPS, advice_low, advice_final_ts),
        ColumnClaim(ADVICE_FINAL, advice_low, advice_final),
        ColumnClaim(BYTECODE_FINAL_COUNTERS, bytecode_low, bytecode_final),
        ColumnClaim(RANGE_LO_FINAL_COUNTERS, range_low, range_lo_final),
        ColumnClaim(RANGE_HI_FINAL_COUNTERS, range_low, range_hi_final),
    ]
    # Register numbers, addresses and pcs are integers: register z is cell z, RAM's word z sits at RAM_BASE + 8z, the
    # advice's at ADVICE_BASE + 8z, instruction z at TEXT_BASE + 4z.
    register_index = int_index_mle(0, 0, register_low)
    ram_index = int_index_mle(RAM_BASE, 3, ram_low)
    ram_initial = sparse_mle(layout.ram, ram_low)
    advice_index = int_index_mle(ADVICE_BASE, 3, advice_low)
    bytecode_index = int_index_mle(TEXT_BASE, 2, bytecode_low)
    bytecode_value = multilinear_eval(layout.bytecode, (*bytecode_low, *alphas))
    # The range arrays are never committed: their addresses g^(j+1) and g^(-2^16 j) are geometric.
    range_lo_index = powers_mle(GEN, GEN, range_low)
    range_hi_index = powers_mle(ONE, RANGE_HI_RATIO, range_low)

    def fingerprints(
        pc: E,
        clock: E,
        register_ts: E,
        register: E,
        ram_ts: E,
        ram: E,
        advice_ts: E,
        advice: E,
        bytecode_count: E,
        range_lo_count: E,
        range_hi_count: E,
    ) -> tuple[E, ...]:
        """The seven framework tuples, each its coordinates weighted by eq(alpha, .); slots past the ones
        named are zero. A side differs only here: push starts the run and seeds every array, pull ends the
        run at the halt slot and finalizes every array with its committed columns."""
        return (
            dot(weights[:3], (SEP_STATE, pc, clock)),
            dot(weights[:4], (SEP_REG, register_index, register_ts, register)),
            dot(weights[:4], (SEP_MEM, ram_index, ram_ts, ram)),
            dot(weights[:4], (SEP_MEM, advice_index, advice_ts, advice)),
            dot(weights[:3], (SEP_BYTECODE, bytecode_index, bytecode_count)) + bytecode_value,
            dot(weights[:3], (SEP_RANGE_LO, range_lo_index, range_lo_count)),
            dot(weights[:3], (SEP_RANGE_HI, range_hi_index, range_hi_count)),
        )

    halt_pc = E(TEXT_BASE + 4 * (2**layout.log_bytecode - 1))  # the run ends on the text's last slot, which is never executed
    # cycle 1, every cell at timestamp g^0: the registers zero, RAM as the statement has it, the advice as the prover has it
    start = fingerprints(E(layout.entry_pc), _gpow(CLOCK_STRIDE), ONE, ZERO, ONE, ram_initial, ONE, advice_initial, ONE, ONE, ONE)
    end = fingerprints(
        halt_pc,
        layout.final_clock,
        register_final_ts,
        register_final,
        ram_final_ts,
        ram_final,
        advice_final_ts,
        advice_final,
        bytecode_final,
        range_lo_final,
        range_hi_final,
    )
    sides = (
        (layout.push, push_layout, start, weights, beta),
        (layout.pull, pull_layout, end, weights, beta),
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
        table_point = tuple(point[:height])
        claims.extend(ColumnClaim(GLOBAL_COLUMN_BASES[table.opcode] + local, table_point, value) for local, value in enumerate(evaluations))
    require(final == claim, "table sumcheck terminal mismatch")
    return claims


# The columns no instruction table owns. They come first in the global column numbering, then one packed flock
# witness per table, then the tables' own columns.
NUM_FRAMEWORK_COLUMNS = 10
REGISTER_FINAL, REGISTER_FINAL_TIMESTAMPS, RAM_FINAL, RAM_FINAL_TIMESTAMPS, ADVICE_INITIAL, ADVICE_FINAL, ADVICE_FINAL_TIMESTAMPS, BYTECODE_FINAL_COUNTERS, RANGE_LO_FINAL_COUNTERS, RANGE_HI_FINAL_COUNTERS = range(NUM_FRAMEWORK_COLUMNS)  # fmt: skip

K_BITS = 64
FLOCK_K_SKIP = log2_ceil(K_BITS)
LOG_PACKING = log2_ceil(K_BITS)  # bits per committed K-element (pcs::pack::LOG_PACKING)
# Flock's zerocheck runs over a cube of at least this many variables: the skip, then seven fixed coordinates.
FLOCK_MIN_LOG_SIZE = 13

# The machine is RISC-V (rv64im). Instruction z sits at TEXT_BASE + 4z, and the register array holds x0..x31, then
# SINK, the cell an instruction with no destination writes: nothing reads it, which is what hardwires x0 to zero.
TEXT_BASE = 0x1000_0000
RAM_BASE = 0x4000_0000  # RAM's word z sits at RAM_BASE + 8z; its first INPUT_WORDS words are the public input
ADVICE_BASE = 0x2000_0000  # the advice's word z sits at ADVICE_BASE + 8z; what it holds before the run is the prover's
# What the regions hold at most, and the most rows a table may announce. These bound the counting arguments the
# memory and lookup proofs rest on, so the verifier checks them before it runs any reduction.
MAX_LOG_TEXT = 26
MAX_LOG_RAM = 27
MAX_LOG_ADVICE = 26
MAX_LOG_ROWS = 32
INPUT_WORDS = 4
LOG_REGISTERS = 6
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
    count: tuple[BusBlock, ...]
    placements: tuple[Placement, ...]
    stack_log: int
    table_log_heights: tuple[int, ...]
    final_clock: E  # the timestamp the run ended on, announced by the prover


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
SEP_RANGE_LO = GEN**3
SEP_RANGE_HI = GEN**4
SEP_REG = GEN**5

# The registers and RAM are read-write, ordered by a clock: access `slot` of cycle `c` carries the timestamp
# g^(4c + slot). A row reads rs1 and rs2, then writes rd last, after the RAM access of a load or a store. A hash row
# reads its two registers, then the sixteen words of its block, and advances the clock past them.
CLOCK_STRIDE = 4
REGISTER_SLOTS = (0, 1, 3)
RAM_SLOT = 2
HASH_WORDS = 16
HASH_OUT_WORD = 4  # the block's words 4 to 7 receive the result
HASH_SLOTS = tuple(range(2, 2 + HASH_WORDS))
HASH_STRIDE = 2 + HASH_WORDS
# A gap between two accesses of one cell is range-checked as two 16-bit chunks, each a read of an array of addresses.
RANGE_LOG = 16
RANGE_HI_RATIO = GEN ** -(2**RANGE_LOG)

ACCESS_KINDS = ("x", "lo", "hi", "cnt_lo", "cnt_hi")


def _accesses(count: int) -> tuple[str, ...]:
    """The columns of a table's accesses, by kind: the previous timestamps, the gap's two chunks, their read counts."""
    return tuple(f"{kind}_{i}" for kind in ACCESS_KINDS for i in range(count))


class Flushes:
    def __init__(self) -> None:
        self.push: list[tuple[Form, ...]] = []
        self.pull: list[tuple[Form, ...]] = []

    def pair(self, push: Sequence[Form], pull: Sequence[Form]) -> None:
        self.push.append(tuple(push))
        self.pull.append(tuple(pull))

    def state(self, columns: Sequence[str], npc: Form, stride: int) -> None:
        """Pull the current state and push the next: `npc`, derived rather than committed, and the clock advanced."""
        pc, ts = _cols(columns, "pc", "ts")
        self.pair((_const(SEP_STATE), npc, _col(ts, stride)), (_const(SEP_STATE), _col(pc), _col(ts)))

    def counted(self, prefix: Sequence[Form], count: int, suffix: Sequence[Form]) -> None:
        """A read of a lookup array: pulled with its count, pushed back with the count advanced."""
        self.pair((*prefix, _col(count, 1), *suffix), (*prefix, _col(count), *suffix))

    def access(self, columns: Sequence[str], separator: E, address: Form, access: int, slot: int, old: Form, new: Form) -> None:
        """Access `access` of the row, at clock slot `slot`: pull the cell as its previous access left it, push it
        back at this access's timestamp, and read the gap's two chunks off the range arrays."""
        ts, x, lo, hi, cnt_lo, cnt_hi = _cols(columns, "ts", *(f"{kind}_{access}" for kind in ACCESS_KINDS))
        self.pair((_const(separator), address, _col(ts, slot), new), (_const(separator), address, _col(x), old))
        self.counted((_const(SEP_RANGE_LO), _col(lo)), cnt_lo, ())
        self.counted((_const(SEP_RANGE_HI), _col(hi)), cnt_hi, ())


def _access_constraints(columns: Sequence[str], slots: Sequence[int]) -> Callable[[Sequence[E]], tuple[E, ...]]:
    """One identity per access, `x * lo = g^slot * ts * hi`: with `lo = g^(d_lo + 1)` and `hi = g^(-2^16 d_hi)`
    read off the range arrays, it says the previous timestamp is `d_lo + 2^16 d_hi + 1` behind this access's own."""
    ts = _cols(columns, "ts")[0]
    triples = [(*_cols(columns, f"x_{i}", f"lo_{i}", f"hi_{i}"), _gpow(slot)) for i, slot in enumerate(slots)]
    return lambda row: tuple(row[x] * row[lo] + shift * row[ts] * row[hi] for x, lo, hi, shift in triples)


# The instruction tables ------------------------------------------------------
#
# One table per instruction class, all of the same shape: the state step, the bytecode read, two register reads and
# one register write. What a class computes is a flock circuit, and every word that circuit reads or writes (`WORDS`)
# is a column here that lives in the circuit's packed witness: the bus is what binds the circuit to the machine. The
# hash class differs in what it accesses: no register write, and the sixteen words of its block, the result's four
# rewritten.

CONTROL_COLUMNS = ("dt", "link", "jalr", "taken")  # the bytecode fields of a class with branches and jumps, and its taken bit
HASH_COLUMNS = (*(f"cell_{k}" for k in range(HASH_WORDS)), *(f"cell_new_{HASH_OUT_WORD + j}" for j in range(4)))
RAM_COLUMNS = {"none": (), "read": ("address", "cell_0"), "write": ("address", "cell_0", "cell_new_0"), "block": HASH_COLUMNS}


BAD_SLOT = 13  # where a bytecode tuple holds a row's `bad` word: past every field of an entry, where the program is zero


def _class_columns(control: bool, ram: str, ports: Sequence[str | None]) -> tuple[str, ...]:
    return (
        "pc", "ts", "a1", "a2", "pc4", "v1", "v2", "flags", *(() if ram == "block" else ("ad", "vd_old", "out")),
        *(CONTROL_COLUMNS if control else ()), *(("imm",) if "imm" in ports else ()), *RAM_COLUMNS[ram], *(("bad",) if "bad" in ports else ()),
        *_accesses(len(_slots(ram))), "cnt_bc",
    )  # fmt: skip


def _slots(ram: str) -> tuple[int, ...]:
    """The clock slots of a row's accesses, in the order of their columns: the registers', then RAM's."""
    if ram == "block":
        return (*REGISTER_SLOTS[:2], *HASH_SLOTS)
    return (*REGISTER_SLOTS, RAM_SLOT) if RAM_COLUMNS[ram] else REGISTER_SLOTS


def _class_flushes(opcode: int, columns: Sequence[str], control: bool, ram: str, ports: Sequence[str | None]) -> Flushes:
    a1, a2, pc4, flags, v1, v2, cnt_bc = _cols(columns, "a1", "a2", "pc4", "flags", "v1", "v2", "cnt_bc")
    # A row without a register write or an immediate reads their constants off the entry: the sink, and zero.
    npc, vd, fields, stride = _col(pc4), _const(ZERO), (), CLOCK_STRIDE
    ad_form, imm_form = _const(SINK), _const(ZERO)
    if ram != "block":
        ad, out = _cols(columns, "ad", "out")
        ad_form, vd = _col(ad), _col(out)
    if "imm" in ports:
        imm_form = _col(_cols(columns, "imm")[0])
    if control:
        dt, link, jalr, taken = _cols(columns, *CONTROL_COLUMNS)
        # What the row derives, each of degree 2: the next pc, and what rd receives.
        npc = _col(pc4) + _prod(taken, dt) + _prod(jalr, out) + _prod(jalr, pc4)
        vd = _col(out) + _prod(link, out) + _prod(link, pc4)
        fields = (_col(dt), _col(link), _col(jalr))
    if ram == "block":
        stride = HASH_STRIDE
    flushes = Flushes()
    flushes.state(columns, npc, stride)
    entry = (_const(_gpow(opcode)), _col(flags), _col(a1), _col(a2), ad_form, imm_form, _col(pc4), *fields)
    if "bad" in ports:
        # What the circuit asserts to be zero rides a slot where the program is zero, so the lookup makes it zero.
        entry = (*entry, *[_const(ZERO)] * (BAD_SLOT - 3 - len(entry)), _col(_cols(columns, "bad")[0]))
    flushes.counted((_const(SEP_BYTECODE), _col(_cols(columns, "pc")[0])), cnt_bc, entry)
    # The register's number comes straight from the bytecode. A read pushes back the value it pulled.
    flushes.access(columns, SEP_REG, _col(a1), 0, REGISTER_SLOTS[0], _col(v1), _col(v1))
    flushes.access(columns, SEP_REG, _col(a2), 1, REGISTER_SLOTS[1], _col(v2), _col(v2))
    if ram != "block":
        flushes.access(columns, SEP_REG, _col(_cols(columns, "ad")[0]), 2, REGISTER_SLOTS[2], _col(_cols(columns, "vd_old")[0]), vd)
    if ram in ("read", "write"):
        # The cell's address is the circuit's word, so an access outside RAM, or a misaligned one, pulls a tuple nothing pushed.
        address, cell, cell_new = _cols(columns, "address", "cell_0", RAM_COLUMNS[ram][-1])
        flushes.access(columns, SEP_MEM, _col(address), 3, RAM_SLOT, _col(cell), _col(cell_new))
    if ram == "block":
        # Word k of the block is the cell at v1 ^ 8k, which is v1 + 8k in the field; the result's words are rewritten.
        for k in range(HASH_WORDS):
            old = _col(_cols(columns, f"cell_{k}")[0])
            new = _col(_cols(columns, f"cell_new_{k}")[0]) if HASH_OUT_WORD <= k < HASH_OUT_WORD + 4 else old
            flushes.access(columns, SEP_MEM, _col(v1) + _const(8 * k), 2 + k, HASH_SLOTS[k], old, new)
    return flushes


@dataclass(frozen=True)
class Table:
    """One instruction class's table: its columns, its bus flushes, its constraints, and its circuit."""

    name: str
    opcode: int  # also its index in TABLES, so g^opcode is its bytecode tag
    control: bool
    ram: str  # how the class uses RAM: a key of RAM_COLUMNS
    circuit: FlockCircuit
    ports: tuple[str | None, ...]  # the circuit's port words in order: a column each, or None for a hint, which is no column
    legal_flags: frozenset[int]

    @property
    def columns(self) -> tuple[str, ...]:
        return _class_columns(self.control, self.ram, self.ports)

    @property
    def flushes(self) -> Flushes:
        return _class_flushes(self.opcode, self.columns, self.control, self.ram, self.ports)

    @property
    def slots(self) -> tuple[int, ...]:
        return _slots(self.ram)

    def constraints(self, row: Sequence[E]) -> tuple[E, ...]:
        return _access_constraints(self.columns, self.slots)(row)

    @property
    def n_constraints(self) -> int:
        return len(self.slots)

    @property
    def width(self) -> int:
        return len(self.columns)

    @property
    def count_columns(self) -> tuple[int, ...]:
        return tuple(i for i, name in enumerate(self.columns) if name.startswith("cnt"))

    @property
    def slot_bits(self) -> int:
        """log2 of the packed words one instance of the circuit occupies."""
        return self.circuit.log_size - LOG_PACKING

    @property
    def min_log_height(self) -> int:
        """A batch is at least eight instances, and the zerocheck's cube at least 2^13 bits."""
        return max(3, FLOCK_MIN_LOG_SIZE - self.circuit.log_size)


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
            ood_point = tuple(transcript.samples(message_log))
            ood_value = transcript.next_scalar()
            pending.append((transcript.sumcheck_round_poly(3, ood_value), lambda x, z=ood_point: eq_eval(z, x)))

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
    # The point r: seven fixed coordinates, the rest sampled.
    r = (*FIXED_CHALLENGES, *transcript.samples(log_n - FLOCK_K_SKIP - len(FIXED_CHALLENGES)))

    # P = P^AB + P^C on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    p_coset = transcript.next_scalars(K_BITS)
    z_skip = transcript.sample()
    v_p = lagrange_interpolate(2 * K_BITS, [ZERO] * K_BITS + list(p_coset), z_skip)

    # nflock quadratic rounds on P, closed by v_a, v_b.
    chi, running = sumcheck(transcript, v_p, 3, r)
    v_a, v_b = transcript.next_scalars(2)
    v_c = running + v_a * v_b
    return ZerocheckResult(z_skip, chi, v_a, v_b, v_c)


@dataclass(frozen=True)
class FlockCircuit:
    """What the reduction needs of a circuit: its block size, where its constant wire sits, and the walk that
    evaluates `e_row^T (A0 + alpha B0) w_col` without building either matrix."""

    log_size: int
    constant_column: int
    bilinear: Callable[[E, Sequence[E], Sequence[E]], E]


def verify_flock_lincheck(circuit: FlockCircuit, zc: ZerocheckResult, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """Lincheck at the quirky point (z_skip, chi): the claim's point, then its 64 slices s."""
    n_rounds = circuit.log_size - FLOCK_K_SKIP
    alpha = transcript.sample()  # batches the two matrix identities, the c claim and the constant-position claim
    # e_row: phi8 Lagrange in the skip coordinate, eq in the slot variables.
    skip_weights = lagrange_weights(K_BITS, zc.z_skip)
    chi_in = zc.chi[:n_rounds]
    e_row = [weight * value for weight in eq_kernel(chi_in) for value in skip_weights]

    # The rounds that bind the high column coordinates (8 for BLAKE2s), leaving 64 unfolded.
    claim = zc.v_a + alpha * zc.v_b + alpha**2 * zc.v_c + alpha**3
    round_challenges, r_lc = sumcheck(transcript, claim, 3, [None] * n_rounds)

    # The residual, then the terminal identity: pin term and c term included.
    # C = I, so the c weight is e_row itself, and both sides being tensors it
    # collapses to eq(chi_in, chi_in_prime) times a 64-term Lagrange combination.
    s = tuple(transcript.next_scalars(K_BITS))
    chi_in_prime = tuple(reversed(round_challenges))
    w_col = [value * weight for weight in eq_kernel(chi_in_prime) for value in s]
    terminal = (
        circuit.bilinear(alpha, e_row, w_col)
        + alpha**2 * eq_eval(chi_in, chi_in_prime) * dot(skip_weights, s)
        + alpha**3 * w_col[circuit.constant_column]
    )
    require(terminal == r_lc, "Flock lincheck terminal mismatch")
    return chi_in_prime + zc.chi[n_rounds:], s


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
    def __init__(self, input_bits: Sequence[int], output_bits: Sequence[int]) -> None:
        self.gates: list[Gate] = []
        words = [-(-bits // 64) for bits in (*input_bits, *output_bits)]
        self.constant_column = 64 * sum(words)
        self.next_slot = self.constant_column + 1
        self.one: Wire = self.push("free", self.constant_column)
        bases = [64 * sum(words[:port]) for port in range(len(words))]
        self.inputs: list[list[Wire]] = [[self.push("free", base + i) for i in range(bits)] for base, bits in zip(bases, input_bits)]
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
ALU_SUB, ALU_WORD, ALU_LT, ALU_LTU, ALU_AND, ALU_OR, ALU_XOR, ALU_CLEAR_BIT0 = range(8)
ALU_BRANCHES = ALU_EQ, ALU_NE, ALU_BLT, ALU_BGE, ALU_BLTU, ALU_BGEU = range(8, 14)
ALU_ALWAYS = 14
ALU_LEGAL_FLAGS = frozenset(
    sum(1 << bit for bit in bits)
    for bits in [(), (ALU_SUB,), (ALU_WORD,), (ALU_SUB, ALU_WORD), (ALU_AND,), (ALU_OR,), (ALU_XOR,), (ALU_CLEAR_BIT0,), (ALU_ALWAYS,)]
    + [(ALU_SUB, bit) for bit in (ALU_LT, ALU_LTU, *ALU_BRANCHES)]
)


def _alu() -> _GateList:
    """(v1, v2, imm, flags) -> (out, taken): add or subtract (and the 32-bit forms), the two comparisons, AND, OR, XOR,
    the six branch conditions, the jumps. `v1 - b` is `v1 + not(b) + 1`, which borrows exactly when it does not carry out."""
    c = _GateList((64, 64, 64, 15), (64, 1))
    v1, v2, imm, flags = c.inputs
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
    out[0] = c.product(c.invert(flags[ALU_CLEAR_BIT0]), out[0])

    taken = flags[ALU_ALWAYS]
    for bit, holds in zip(ALU_BRANCHES, (eq, ne, lt, c.invert(lt), ltu, c.invert(ltu))):
        taken = c.xor(taken, c.product(flags[bit], holds))
    for i, wire in enumerate(out):
        c.output(0, i, wire)
    c.output(1, 0, taken)
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


def _shift_bytes(c: _GateList, x: Sequence[Wire], amount: Sequence[Wire], left: bool) -> list[Wire]:
    """`x` shifted by `8 * amount` bits, `amount` being three bits."""
    x = list(x)
    for stage, bit in enumerate(amount):
        by = 8 << stage
        moved = [x[i - by] if i >= by else None for i in range(64)] if left else [x[i + by] if i + by < 64 else None for i in range(64)]
        x = [c.mux(bit, moved[i], x[i]) for i in range(64)]
    return x


def _bus_address(c: _GateList, v1: Sequence[Wire], imm: Sequence[Wire], log_width: Sequence[Wire]) -> tuple[list[Wire], list[Wire], list[Wire]]:
    """A load's or a store's address `v1 + imm`, the width's thresholds (at least 2 bytes, at least 4, exactly 8), and
    what goes on the memory bus: the address of the 64-bit cell, with the bits that misalign the access left in.
    A cell's address is a multiple of 8, so a misaligned access names no cell at all."""
    address = _add(c, v1, imm)
    thresholds = [c.either(log_width[0], log_width[1]), log_width[1], c.product(log_width[0], log_width[1])]
    bus = [c.product(address[i], thresholds[i]) for i in range(3)] + address[3:]
    return address, thresholds, bus


def _load() -> _GateList:
    """(v1, imm, flags, cell) -> (address, out): the bytes of `cell` the address names, extended to 64 bits."""
    c = _GateList((64, 64, 3, 64), (64, 64))
    v1, imm, flags, cell = c.inputs
    address, (ge2, ge4, eq8), bus = _bus_address(c, v1, imm, flags[:2])
    value = _shift_bytes(c, cell, address[:3], left=False)
    # The extension: the value's top bit, which the width places, if the load is signed.
    sign: Wire = None
    for width, bit in ((c.invert(ge2), 7), (c.xor(ge2, ge4), 15), (c.xor(ge4, eq8), 31)):
        sign = c.xor(sign, c.product(width, value[bit]))
    extension = c.product(flags[2], sign)
    for i, wire in enumerate(bus):
        c.output(0, i, wire)
    for i in range(64):
        keeps = None if i < 8 else ge2 if i < 16 else ge4 if i < 32 else eq8
        c.output(1, i, value[i] if i < 8 else c.mux(keeps, value[i], extension))
    return c


def _store() -> _GateList:
    """(v1, v2, imm, flags, cell) -> (address, new cell, out): `cell` with the bytes the address names replaced by the
    low bytes of `v2`. `out` is what the row writes to its destination, the sink: zero."""
    c = _GateList((64, 64, 64, 2, 64), (64, 64, 64))
    v1, v2, imm, flags, cell = c.inputs
    address, thresholds, bus = _bus_address(c, v1, imm, flags)
    value = _shift_bytes(c, v2, address[:3], left=True)
    # Byte j is written when it shares the access's block: bit k of j equals bit k of the address wherever the
    # width does not already span both.
    spans = [[c.either(c.invert(address[k]), thresholds[k]), c.either(address[k], thresholds[k])] for k in range(3)]
    for i, wire in enumerate(bus):
        c.output(0, i, wire)
    for j in range(8):
        written = c.product(c.product(spans[0][j & 1], spans[1][j >> 1 & 1]), spans[2][j >> 2])
        for i in range(8 * j, 8 * j + 8):
            c.output(1, i, c.mux(written, value[i], cell[i]))
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


HASH_PORTS = ("v2", "flags", *(f"cell_{k}" for k in (*range(4), *range(8, 16))), *(f"cell_new_{HASH_OUT_WORD + j}" for j in range(4)))
HASH_FINAL = 2**32 - 1

TABLES = (
    Table("alu", 0, True, "none", _alu().circuit(), ("v1", "v2", "imm", "flags", "out", "taken"), ALU_LEGAL_FLAGS),
    # A load's flags are log2 of its width in bytes, then whether it sign-extends; a store's, log2 of its width.
    Table("load", 1, False, "read", _load().circuit(), ("v1", "imm", "flags", "cell_0", "address", "out"), frozenset(range(7))),
    Table(
        "store", 2, False, "write", _store().circuit(), ("v1", "v2", "imm", "flags", "cell_0", "address", "cell_new_0", "out"), frozenset(range(4))
    ),
    # A shift's flags: right, arithmetic (with right), 32-bit. A product's: 32-bit; its high word's: which operands are signed.
    Table("shift", 3, False, "none", _shift().circuit(), ("v1", "v2", "imm", "flags", "out"), frozenset((0, 1, 3, 4, 5, 7))),
    Table("mul", 4, False, "none", _mul().circuit(), ("v1", "v2", "flags", "out"), frozenset((0, 1))),
    Table("mulh", 5, False, "none", _mulh().circuit(), ("v1", "v2", "flags", "out"), frozenset((0, 1, 3))),
    # A division's flags: signed, remainder, 32-bit. Its two hints are in its witness and in no column.
    Table("div", 6, False, "none", _div().circuit(), ("v1", "v2", "flags", None, None, "out", "bad"), frozenset(range(8))),
    # The BLAKE2s precompile: the counter is v2 and the flags are the finalization word, all ones on the last block.
    Table("hash", 7, False, "block", _blake2s().circuit(), HASH_PORTS, frozenset((0, HASH_FINAL))),
)

TABLE_WIDTHS = tuple(t.width for t in TABLES)
WITNESS_COLUMNS = tuple(NUM_FRAMEWORK_COLUMNS + t.opcode for t in TABLES)  # each table's packed flock witness
GLOBAL_COLUMN_BASES = tuple(NUM_FRAMEWORK_COLUMNS + len(TABLES) + sum(TABLE_WIDTHS[:table]) for table in range(len(TABLES)))


def check_bytecode(bytecode: Sequence[K]) -> None:
    """The proof system is sound for any decoded table, so what makes one RISC-V is checked here: an entry some table
    can read names two registers to read and a cell other than x0 to write, its successor is pc + 4, and its flags
    are ones its class defines. An entry with no tag can be read by no table: a run reaching one has no proof."""
    size = len(bytecode) // 2**BUS_BITS
    fields = [[int(word) for word in bytecode[slot * size : (slot + 1) * size]] for slot in range(2**BUS_BITS)]
    tag, flags, a1, a2, ad, imm, pc4, _, link, jalr = fields[3:13]
    require(not any(any(column) for column in fields[:3] + fields[13:]), "a bytecode slot outside an entry's fields is nonzero")
    tags = {int(_gpow(table.opcode)): table for table in TABLES}
    for z in range(size):
        if tag[z] == 0:
            continue
        table = tags.get(tag[z])
        require(table is not None, "a bytecode entry names no class")
        require(a1[z] < 32 and a2[z] < 32 and 1 <= ad[z] <= SINK, "a bytecode entry misnames a register")
        require(pc4[z] == TEXT_BASE + 4 * z + 4, "a bytecode entry's successor is not pc + 4")
        require(flags[z] in table.legal_flags, "a bytecode entry's flags are not its class's")
        require(link[z] <= 1 and jalr[z] <= 1, "a bytecode selector is not a bit")
        require(table.ram != "block" or (ad[z] == SINK and imm[z] == 0), "a hash entry writes a register or has an immediate")


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
        2 <= log_ram <= MAX_LOG_RAM and all(offset + len(words) <= 2**log_ram for offset, words in ram),
        "RAM does not hold its image",
    )
    require(0 <= log_advice <= MAX_LOG_ADVICE, "the advice exceeds its region")

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

    # Every column's log size, in global order: the framework's, the flock witnesses', then each table's block.
    witness_kappas = [height + table.slot_bits for table, height in zip(TABLES, table_log_heights)]
    kappas = [LOG_REGISTERS, LOG_REGISTERS, log_ram, log_ram, log_advice, log_advice, log_advice, log_bytecode, RANGE_LOG, RANGE_LOG, *witness_kappas]
    for table in TABLES:
        kappas += [table_log_heights[table.opcode]] * table.width

    # A circuit word gets no block of its own: it is committed inside its table's flock witness, whose ports
    # interleave, so it sits at that witness's offset behind its own port's bits. Same width either way.
    words = {
        GLOBAL_COLUMN_BASES[table.opcode] + _cols(table.columns, name)[0]: (table, port)
        for table in TABLES
        for port, name in enumerate(table.ports)
        if name
    }
    blocks = {column: kappa for column, kappa in enumerate(kappas) if column not in words}
    block_offsets, total_log = stack_offsets(list(blocks.values()))
    offsets = dict(zip(blocks, block_offsets))
    stack_log = max(MIN_STACKED_LOG, total_log)  # Floor at the PCS minimum

    def placement(column: int, kappa: int) -> Placement:
        if column not in words:
            return Placement(kappa, offsets[column])
        table, port = words[column]
        return Placement(kappa, offsets[WITNESS_COLUMNS[table.opcode]] + port, table.slot_bits)

    placements = [placement(column, kappa) for column, kappa in enumerate(kappas)]
    return Layout(
        log_bytecode,
        bytecode,
        entry_pc,
        log_ram,
        log_advice,
        ram,
        tuple(push),
        tuple(pull),
        tuple(count),
        tuple(placements),
        stack_log,
        tuple(table_log_heights),
        final_clock,
    )


def verify_flock(circuit: FlockCircuit, log_height: int, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """The reduction in protocol order: zerocheck, then lincheck. What it leaves is the
    point and the 64 claims s[i] = z(i, point), i < 64, for ring switching to bind."""
    zc = verify_flock_zerocheck(circuit.log_size + log_height, transcript)
    return verify_flock_lincheck(circuit, zc, transcript)


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


def ring_switch(families: Sequence[tuple[MultilinearPoint, Sequence[E]]], transcript: Transcript) -> list[tuple[E, Callable[[Sequence[E]], E]]]:
    """Each family of 64 claims s[i] = z(i, point) becomes one dense claim `sum_u W(u) q(u) = target` on its own packed witness.

    Draw Phi once every family is fixed, the one map serving them all, then take the target
    `T = sum_i x^i Phi(s_i)` against the MLE-friendly weight `W(u) = Phi(eq(point, u))`.
    Returns each family's target and its W as a closure."""
    challenges = transcript.samples(len(RING_MAP_SHIFTS))
    # The same map as a Frobenius sum, `Phi(a) = sum_k c_k a^(2^k)` for k < 64.
    coefficients = [reduce(mul, (f ** (2 ** (k % s)) for f, s in zip(challenges, RING_MAP_SHIFTS) if k & s), ONE) for k in range(K_BITS)]

    def claim(point: MultilinearPoint, s: Sequence[E]) -> tuple[E, Callable[[Sequence[E]], E]]:
        target = poly_eval([_phi(value, challenges) for value in s], GEN)
        return target, lambda r_prime: _ring_weight(point, r_prime, coefficients)

    return [claim(point, s) for point, s in families]


# Stacked opening -------------------------------------------------------------


type StackClaim = tuple[Callable[[Sequence[E]], E], E]  # the weight it puts on the stack, and the value it claims for it


def verify_stacked_opening(transcript: Transcript, root: Digest, stack_log: int, log_inv_rate: int, claims: Sequence[StackClaim]) -> None:
    """Discharge every claim on the committed stack in one opening: the same powers of one challenge
    batch the values into the target, and the weights into the basis WHIR evaluates at its terminal point.
    """
    weights, values = zip(*claims, strict=True)
    scales = powers(transcript.sample(), len(claims))
    verify_whir(transcript, stack_log, log_inv_rate, dot(scales, values), root, lambda point: dot(scales, [weight(point) for weight in weights]))


def verify_execution(
    bytecode: Sequence[K],
    entry_pc: int,
    log_ram: int,
    log_advice: int,
    image: Sequence[int],
    public_input: Sequence[int],
    output: Sequence[int],
    proof: Proof,
) -> None:
    """The statement: the program whose decoded table is `bytecode`, started at `entry_pc` on a RAM of `2^log_ram` words
    holding `public_input` then `image`, with an advice region of `2^log_advice` words holding whatever the prover put
    there, halts on `exit` with a0..a3 holding `output`."""
    require(len(public_input) == INPUT_WORDS and len(output) == 4, "the input and the output are four words each")
    check_bytecode(bytecode)
    # Everything public and fixed is one digest, which seeds the transcript; every variable-length part is length-framed.
    halt_pc = TEXT_BASE + 4 * (len(bytecode) // 2**BUS_BITS - 1)
    preimage = b"leanvm-rv64im-1" + pack("<Q", len(bytecode)) + b"".join(word.to_bytes() for word in bytecode)
    preimage += pack("<5Q", entry_pc, halt_pc, log_ram, log_advice, len(image)) + pack(f"<{len(image)}Q", *image)
    digest = blake2s_hash(preimage)
    transcript = Transcript(proof, blake2s_hash(digest.value + pack(f"<{INPUT_WORDS}Q", *public_input)), [K(word) for word in output])

    # 1] table log-sizes, log-inv-rate in WHIR, and the clock the run ended on (a K element)
    announced = transcript.next_scalars(2 + len(TABLES))
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced value has a nonzero high limb")
    table_logs = tuple(int(value.c0) for value in announced[: len(TABLES)])
    log_inverse_rate = int(announced[-2].c0)
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    ram = ((0, public_input), (INPUT_WORDS, image))
    layout = build_layout(bytecode, entry_pc, log_ram, log_advice, ram, table_logs, announced[-1])
    require(MIN_STACKED_LOG <= layout.stack_log <= MAX_STACKED_LOG, "committed size outside the PCS window")

    # 2] parse WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    root = Digest.from_halves(*transcript.next_scalars(2))

    # 3] Bus: one batched GKR over the push, pull and count trees, then the leaf decomposition, which leaves each table a degree-2 claim.
    bus = verify_bus_balance(layout, transcript)

    # 4] One batched (back-loaded) "table sumcheck" over all the tables, at the bus point, proving the target the three
    # leaf claims derive and that constraints vanish. Every table takes a disjoint range of xi powers for its constraints
    xi = transcript.sample()
    n_constraints = sum(table.n_constraints for table in TABLES)
    xi_powers = powers(xi, n_constraints + 3)  # one power per constraint, then one per bus side, shared by every table
    constraint_powers, form_powers = xi_powers[:n_constraints], xi_powers[n_constraints:]
    target = dot(form_powers, bus.totals)
    table_sumcheck_claims = table_sumcheck(layout.table_log_heights, bus.forms, constraint_powers, form_powers, bus.point, target, transcript)
    claims = [*bus.claims, *table_sumcheck_claims]

    # 5] the exit: a7 holds `exit` and a0..a3 the output when the run ends. A register's final value is the final
    # registers' column at the Boolean point naming it, a claim the verifier computes rather than receives.
    for register, value in ((SYSCALL_REGISTER, SYS_EXIT), *zip(OUTPUT_REGISTERS, output)):
        point = tuple(ONE if register >> bit & 1 else ZERO for bit in range(LOG_REGISTERS))
        claims.append(ColumnClaim(REGISTER_FINAL, point, E(value)))

    # 6] each class's circuit via Flock, one reduction per table over its own packed witness
    families = [verify_flock(table.circuit, layout.table_log_heights[table.opcode], transcript) for table in TABLES]

    # 7] Ring-switching
    # Each claim is supported on its witness's region of the stack, so its weight carries the
    # placement's selector, and they lead the batch, taking the first powers.
    def on_region(placement: Placement, target: E, weight: Callable[[Sequence[E]], E]) -> StackClaim:
        return (lambda x: placement.eq_above(x) * weight(x[: placement.variables]), target)

    regions = [layout.placements[column] for column in WITNESS_COLUMNS]
    ringswitches = [on_region(region, *claim) for region, claim in zip(regions, ring_switch(families, transcript), strict=True)]
    verify_stacked_opening(transcript, root, layout.stack_log, log_inverse_rate, [*ringswitches, *(c.on_stack(layout) for c in claims)])
    transcript.finish()


def protocol_constants() -> str:
    """Every constant this verifier shares with the Rust one, as sorted `name value` lines. The two are written out
    twice on purpose, so something has to hold them together: `lean_vm`'s `constants_match_the_python_verifier`
    renders the same lines from its own side and diffs them. Lists are comma-separated."""
    scalars = {
        "ADVICE_BASE": ADVICE_BASE,
        "BAD_SLOT": BAD_SLOT,
        "BUS_BITS": BUS_BITS,
        "CLOCK_STRIDE": CLOCK_STRIDE,
        "FLOCK_K_SKIP": FLOCK_K_SKIP,
        "FLOCK_MIN_LOG_SIZE": FLOCK_MIN_LOG_SIZE,
        "HASH_OUT_WORD": HASH_OUT_WORD,
        "HASH_STRIDE": HASH_STRIDE,
        "HASH_WORDS": HASH_WORDS,
        "INITIAL_FOLDING_FACTOR": INITIAL_FOLDING_FACTOR,
        "INPUT_WORDS": INPUT_WORDS,
        "LOG_PACKING": LOG_PACKING,
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
        "RANGE_LOG": RANGE_LOG,
        "RESIDUAL_MAX_LOG": RESIDUAL_MAX_LOG,
        "RS_DOMAIN_INITIAL_REDUCTION_FACTOR": RS_DOMAIN_INITIAL_REDUCTION_FACTOR,
        "RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR": RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR,
        "SINK": SINK,
        "SUBSEQUENT_FOLDING_FACTOR": SUBSEQUENT_FOLDING_FACTOR,
        "SYSCALL_REGISTER": SYSCALL_REGISTER,
        "SYS_EXIT": SYS_EXIT,
        "TEXT_BASE": TEXT_BASE,
    }
    lines = [f"{name} {value}" for name, value in scalars.items()]
    lines.append("OUTPUT_REGISTERS " + ",".join(str(r) for r in OUTPUT_REGISTERS))
    lines.append("REGISTER_SLOTS " + ",".join(str(s) for s in REGISTER_SLOTS))
    for table in TABLES:
        prefix = f"TABLE.{table.name}"
        lines.append(f"{prefix}.opcode {table.opcode}")
        lines.append(f"{prefix}.k_log {table.circuit.log_size}")
        lines.append(f"{prefix}.const_pos {table.circuit.constant_column}")
        lines.append(f"{prefix}.slot_bits {table.slot_bits}")
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
        help="little-endian 64-bit words: the entry pc, log2 of RAM's words, log2 of the advice's, the program's image (its length, then its words), the four input words, the four output words",
    )
    parser.add_argument("stream", type=Path, help="the proof's scalar stream, 24-byte little-endian field elements")
    parser.add_argument("merkle_openings", type=Path, help="every Merkle opening: its leaf's words, then its sibling digests")
    arguments = parser.parse_args(argv)
    try:
        encoded_bytecode = arguments.bytecode.read_bytes()
        require(len(encoded_bytecode) % 8 == 0, "bytecode is not a whole number of 64-bit words")
        bytecode = [K(int.from_bytes(encoded_bytecode[i : i + 8], "little")) for i in range(0, len(encoded_bytecode), 8)]
        encoded_public = arguments.public.read_bytes()
        require(len(encoded_public) % 8 == 0 and len(encoded_public) >= 12 * 8, "the public words are malformed")
        entry_pc, log_ram, log_advice, image_length, *rest = unpack(f"<{len(encoded_public) // 8}Q", encoded_public)
        require(len(rest) == image_length + INPUT_WORDS + 4, "the public words are malformed")
        image, public_input, output = rest[:image_length], rest[image_length:-4], rest[-4:]
        proof = Proof.load(arguments.stream, arguments.merkle_openings)
        verify_execution(bytecode, entry_pc, log_ram, log_advice, image, public_input, output, proof)
    except (OSError, ValueError, KeyError, VerificationError) as exc:
        parser.exit(1, f"verification failed: {exc}\n")
    print("verification succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
