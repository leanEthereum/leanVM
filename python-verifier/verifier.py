from __future__ import annotations

from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from functools import reduce
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


# The hash and digests --------------------------------------------------------

# Keccak-256 (Ethereum's hash): 136-byte blocks, the last holding the remaining 0 to 135
# bytes and the padding 0x01 || 0^* || 0x80.
RATE = 136
STATE_LANES = 25
ROUNDS = 24
PAD_FIRST = 0x01  # the padding's first byte, after the message; FIPS 202's 256-bit hash would put 0x06
PAD_LAST = 0x80


def keccak_hash(data: bytes) -> Digest:
    """The 32-byte hash of `data`."""
    blocks = len(data) // RATE + 1
    padded = bytearray(data) + bytes(blocks * RATE - len(data))
    padded[len(data)] ^= PAD_FIRST
    padded[-1] ^= PAD_LAST
    state = [0] * STATE_LANES
    for b in range(blocks):
        state = keccak_f([lane ^ word for lane, word in zip(state, unpack("<17Q", padded[RATE * b : RATE * (b + 1)]))] + state[17:])
    return Digest(pack("<4Q", *state[:4]))


@dataclass(frozen=True, slots=True)
class Digest:
    """256 bits"""

    value: bytes

    def __post_init__(self) -> None:
        require(len(self.value) == 32, "a digest is 256 bits")

    def words(self) -> tuple[int, int, int, int]:
        """Its four 64-bit words, the form the sponge state holds it in."""
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
    return (max(value, 1) - 1).bit_length()


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


def padding_weight(point: Sequence[E], n: int) -> E:
    """`pad_n(point)`, the multilinear extension of `[z >= n]`, `n <= 2^len(point)` (lemma lem:suffix)."""
    pad = ONE
    for k, r in enumerate(point):
        b = E(n >> k & 1)
        pad = (ONE + b) * r + (ONE + b + r) * pad
    return (ONE + E(n >> len(point) & 1)) * pad


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
    """Where something sits in the stacked cube: a claim's point fills the low `variables` coordinates, the bits of `index` fixing the rest."""

    variables: int
    index: int

    def stack_point(self, point: MultilinearPoint, stack_log: int) -> MultilinearPoint:
        return tuple(point) + _selector_point(self.index >> self.variables, stack_log - self.variables)

    def eq_above(self, point: Sequence[E]) -> E:
        """eq weight of the coordinates above the window."""
        bits = _selector_point(self.index >> self.variables, len(point) - self.variables)
        return eq_eval(bits, point[self.variables :])


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
# A duplex sponge over the VM's KECCAK step, in overwrite mode. The rate is lanes 0..16 and the
# capacity lanes 16..25. Up to four absorbed scalars wait; a permutation writes scalar i over lanes
# 4i..4i+4 (three limbs and a tag), zeroes the rest of the rate and keeps the capacity. A fifth
# scalar, or a challenge, permutes what waits, and every challenge takes a permutation of its own.

DS_OBSERVE = 1
DS_POW_NONCE = 4
RATE_SCALARS = 4
LANE_MASK = 2**64 - 1


def keccak_f(lanes: Sequence[int]) -> list[int]:
    """Keccak-f[1600]."""
    a = list(lanes)

    def rot(x: int, n: int) -> int:
        return ((x << n) | (x >> (64 - n))) & LANE_MASK if n else x

    for rc in KECCAK_RC:
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        a = [a[i] ^ c[(i - 1) % 5] ^ rot(c[(i + 1) % 5], 1) for i in range(STATE_LANES)]
        b = [0] * STATE_LANES
        for i in range(STATE_LANES):
            b[KECCAK_PI[i]] = rot(a[i], KECCAK_RHO[i])
        a = [b[i] ^ (~b[i - i % 5 + (i + 1) % 5] & LANE_MASK & b[i - i % 5 + (i + 2) % 5]) for i in range(STATE_LANES)]
        a[0] ^= rc
    return a


class Transcript:
    def __init__(self, proof: Proof, fiat_shamir_IV: Digest, public_input: Digest) -> None:
        self.proof = proof
        self.state = keccak_f([*fiat_shamir_IV.words(), *public_input.words(), *[0] * 17])
        self.pending: list[tuple[E, int]] = []
        self.stream_offset = 0  # in E field elements
        self.opening_offset = 0  # in bytes

    def _duplex(self) -> None:
        rate = [lane for value, tag in self.pending for lane in (value.c0.value, value.c1.value, value.c2.value, tag)]
        self.state = keccak_f([*rate, *[0] * (16 - len(rate)), *self.state[16:]])
        self.pending = []

    def _absorb(self, value: E, tag: int) -> None:
        if len(self.pending) == RATE_SCALARS:
            self._duplex()
        self.pending.append((value, tag))

    def observe(self, value: E) -> None:
        self._absorb(value, DS_OBSERVE)

    def sample(self) -> E:
        self._duplex()
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
        self._absorb(nonce, DS_POW_NONCE)
        challenge = self.sample()
        require(nonce == ZERO if bits == 0 else challenge.c0.value & (2**bits - 1) == 0, "invalid grinding nonce")

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
            node = keccak_hash(leaf)
            for level in range(height):
                sibling = self._merkle_data(32)
                left, right = (node.value, sibling) if query >> level & 1 == 0 else (sibling, node.value)
                node = keccak_hash(left + right)
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
    point: list[E] = []
    values = (shared, shared, count)  # 3 grand product GKR are batched together: push, pull, count

    layer = depth
    while layer > 0:
        # Two levels a step. An odd depth starts with one.
        step = 1 if layer % 2 else 2
        combiner = transcript.sample()
        claim = poly_eval(values, combiner)
        # The product is degree 2^step, so one more coefficient than that per round.
        x, claim = sumcheck(transcript, claim, 2**step + 1, point)

        children = [transcript.next_scalars(2**step) for _ in range(3)]
        products = [reduce(mul, child) for child in children]
        require(claim == poly_eval(products, combiner), f"GKR layer {layer}: children do not match the sumcheck")

        y = transcript.samples(step)
        values = [multilinear_eval(child, y) for child in children]
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

    log_rows: int  # the owner's height: the block spans 2^log_rows rows
    rows: int  # ...of which the first `rows` flush, the rest being padding rows, whose leaves are 1
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

    def on_stack(self, layout: Layout) -> StackClaim | None:
        """None for a column nothing commits, whose claim never reaches the stack."""
        placement = layout.placements[self.column]
        if placement is None:
            return None
        point = placement.stack_point(self.point, layout.stack_log)
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
    memory_index = index_mle(memory_low)
    bytecode_index = index_mle(bytecode_low)
    bytecode_value = multilinear_eval(layout.bytecode, (*bytecode_low, *alphas))

    def fingerprints(pc: E, memory_count: E, bytecode_count: E) -> tuple[E, E, E]:
        """The three framework tuples, each its coordinates weighted by eq(alpha, .); slots past the ones
        named are zero. A side differs only here: push seeds each array at count one, pull finalizes it
        with the committed final count and ends at the last pc. Both boundaries sit in frame 0."""
        return (
            dot(weights[:3], (SEP_STATE, pc, _gpow(0))),
            dot(weights[:6], (SEP_MEM, memory_index, memory_count, *memory)),
            dot(weights[:3], (SEP_BYTECODE, bytecode_index, bytecode_count)) + bytecode_value,
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
        # That form is summed over the padding rows too, whose leaves hold 1 instead: the difference is public.
        padding_rows = ZERO
        for selector, block in zip(table_selectors, blocks, strict=True):
            block_form = _const(side_beta)
            for slot, coordinate in enumerate(block.coordinates):
                block_form.add_scaled(coordinate, side_weights[slot])  # the fingerprint, one tuple slot at a time
            forms[block.owner][side].add_scaled(block_form, selector)
            padding = TABLES[block.owner].padding
            padding_rows += selector * padding_weight(point[: block.log_rows], block.rows) * (block_form.evaluate(padding.__getitem__) + ONE)
        # The leaves outside every block hold 1.
        ones_padding = E.sum(framework_selectors + table_selectors) + ONE
        totals.append(tree_values[side] + known + ones_padding + padding_rows)  # what the forms owe: the GKR value, less framework and padding

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
) -> list[tuple[MultilinearPoint, tuple[E, ...]]]:
    """Each table's point and its columns' evaluations there."""
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
    rows = []
    for table, height, forms, weight in zip(TABLES, table_log_heights, bus_forms, weights, strict=True):
        evaluations = tuple(transcript.next_scalars(table.width))
        summand = dot(constraint_powers[cursor : cursor + table.n_constraints], table.constraints(evaluations))
        final += weight * (summand + dot(form_powers, [form.evaluate(evaluations.__getitem__) for form in forms]))
        cursor += table.n_constraints
        rows.append((tuple(point[:height]), evaluations))
    require(final == claim, "table sumcheck terminal mismatch")
    return rows


RELATION_LABEL = (
    b"leanVM keccak GKR: keccak-f in two cell layouts, depth 12, packs of 16 in degree 23, lane slots then table columns, output claimed by the bus"
)

# The columns no instruction table owns. They come first in the global column numbering, the tables after.
NUM_GLOBAL_COLUMNS = 6
MEMORY_0, MEMORY_1, MEMORY_2, MEMORY_FINAL_COUNTERS, BYTECODE_FINAL_COUNTERS, QKECCAK = range(NUM_GLOBAL_COLUMNS)

K_BITS = 64

# The Keccak reduction commits a step's state every KECCAK_DEPTH rounds but the output, a word per step
# in each of 25 columns. Those columns are placed as one aligned run, q_keccak, a column of the run being
# a slot: lane l of the state after KECCAK_DEPTH * m rounds is slot 25 m + l.
KECCAK_DEPTH = 12
KECCAK_SEGMENTS = ROUNDS // KECCAK_DEPTH
KECCAK_SEGMENT_BITS = log2_ceil(KECCAK_SEGMENTS)
QKECCAK_SLOT_BITS = log2_ceil(STATE_LANES * KECCAK_SEGMENTS)
KECCAK_MIN_STEPS_LOG = 9  # the reduction is sized for at least one block of 512 steps
KECCAK_CELLS = 13  # a sponge state, read and written by KECCAK
KECCAK_BITS = 64 * STATE_LANES
KECCAK_LOCAL_BITS = 11  # a bit position is z + 64 * lane, in a cube of 2048
KECCAK_LANE_BITS = 5


@dataclass(frozen=True)
class Layout:
    log_memory: int
    log_bytecode: int
    bytecode: Sequence[K]
    push: tuple[BusBlock, ...]
    pull: tuple[BusBlock, ...]
    count: tuple[BusBlock, ...]
    placements: tuple[Placement | None, ...]  # None for a column nothing commits: the KECCAK output lanes
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

    @property
    def padding(self) -> tuple[E, ...]:
        """The row a padding row holds: zero, but for KECCAK's output lanes, a padding row permuting zeros."""
        padding = [ZERO] * self.width
        if self.opcode == OP_KECCAK:
            padding[KECCAK_OUT : KECCAK_OUT + STATE_LANES] = map(E, keccak_f([0] * STATE_LANES))
        return tuple(padding)


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


# The lanes each of a sponge state's thirteen cells holds, (lo, hi), in the even layout or
# the odd one, None marking a limb that holds no lane: nine rate cells, lanes 0..16
# two to a cell then lane 16 in a low limb (even), or lane 0 in a high limb,
# then lanes 1..17 two to a cell (odd), then the capacity lanes 17..25.
def _keccak_cell_lanes(odd: bool) -> tuple[tuple[int | None, int | None], ...]:
    def lanes(c: int) -> tuple[int | None, int | None]:
        if c >= 9 or (odd and c >= 1):
            return (2 * c - 1, 2 * c)
        if odd:
            return (None, 0)
        return (16, None) if c == 8 else (2 * c, 2 * c + 1)

    return tuple(lanes(c) for c in range(KECCAK_CELLS))


def _layout_limb(even: int | None, odd: int | None, flag: int, missing: int | None) -> Form:
    """A cell limb holding lane `even` in the even layout and `odd` in the odd one, as `flag` selects: a + flag*(a + b)."""
    a = even if even is not None else missing
    b = odd if odd is not None else missing
    if a == b:
        return _const(ZERO) if a is None else _col(a)
    return Form.sum([*([_col(a), _prod(flag, a)] if a is not None else []), *([_prod(flag, b)] if b is not None else [])])


def _flushes_keccak() -> Flushes:
    pc, fp, cnt_bc, free = _cols(KECCAK_COLUMNS, "pc", "fp", "cnt_bc", "free")
    o_m = _cols(KECCAK_COLUMNS, "o_m0", "o_m1", "o_m2", "o_m3")
    o_tail, o_b8, o_cap, o_out, odd_in, odd_out = _cols(KECCAK_COLUMNS, "o_tail", "o_b8", "o_cap", "o_out", "odd_in", "odd_out")
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, OP_KECCAK, tuple(_col(i) for i in (*o_m, o_tail, o_b8, o_cap, o_out, odd_in, odd_out)))

    # The thirteen cells read (four addressed ones, the tail run, b8, the cap run), then the
    # thirteen written, each holding its lanes in the layout its flag names: a read cell's
    # free lane is the column `free`, a written one's zero.
    def address(cell: int) -> Form:
        if cell < 4:
            return _prod(fp, o_m[cell])
        if cell < 8:
            return _prod(fp, o_tail, cell - 4)
        return _prod(fp, o_b8) if cell == 8 else _prod(fp, o_cap, cell - 9)

    even, odd = _keccak_cell_lanes(False), _keccak_cell_lanes(True)
    for side, (lanes, flag, missing) in enumerate(((KECCAK_IN, odd_in, free), (KECCAK_OUT, odd_out, None))):

        def lane(lane: int | None, lanes: int = lanes) -> int | None:
            return None if lane is None else lanes + lane

        for cell in range(KECCAK_CELLS):
            values = [_layout_limb(lane(even[cell][h]), lane(odd[cell][h]), flag, missing) for h in (0, 1)] + [_const(ZERO)]
            flushes.memory(address(cell) if side == 0 else _prod(fp, o_out, cell), KECCAK_CNT + KECCAK_CELLS * side + cell, values)
    return flushes


OP_XOR, OP_MUL, OP_SET, OP_DEREF, OP_JUMP, OP_KECCAK = range(6)

ARITH_COLUMNS = ("pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a", "cnt_b", "cnt_c", "cnt_bc",)  # fmt: skip
SET_COLUMNS = ("pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc")
DEREF_COLUMNS = ("pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2",  "cnt_ptr", "cnt_target", "cnt_local", "cnt_bc",)  # fmt: skip
JUMP_COLUMNS = ("pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc", "w", "b",)  # fmt: skip
KECCAK_COLUMNS = (
    "pc", "fp", "o_m0", "o_m1", "o_m2", "o_m3", "o_tail", "o_b8", "o_cap", "o_out", "odd_in", "odd_out",
    # The read limb that holds no lane.
    "free",
    # The fifty value lanes: an input lane is a slot of q_keccak (below), and an output lane is not
    # committed at all, the claims on it being where the Keccak reduction starts.
    *(f"in_{lane}" for lane in range(STATE_LANES)), *(f"out_{lane}" for lane in range(STATE_LANES)),
    # ...and the read counts, each cell read then each written, committed here like every other column.
    *(f"cnt_{cell}" for cell in range(2 * KECCAK_CELLS)), "cnt_bc",
)  # fmt: skip
KECCAK_IN, KECCAK_OUT, KECCAK_CNT = (KECCAK_COLUMNS.index(name) for name in ("in_0", "out_0", "cnt_0"))
# Which slot of q_keccak each local KECCAK column is. The states take the first QKECCAK_SLOTS, the input
# lanes among them; the run is a power of two wide, so the slots left over carry the table's own first
# committed columns, which the reduction weighs nothing on and the stack then holds only once.
QKECCAK_SLOTS = STATE_LANES * KECCAK_SEGMENTS
QKECCAK_SPARE = 2**QKECCAK_SLOT_BITS - QKECCAK_SLOTS
_KECCAK_COMMITTED = [local for local in range(len(KECCAK_COLUMNS)) if not KECCAK_IN <= local < KECCAK_CNT]
# The guard the prover and the Rust verifier carry too: every spare slot needs a committed column of
# the table to put in it. True at this depth, not at every divisor of 24, and the three must agree.
assert len(_KECCAK_COMMITTED) >= QKECCAK_SPARE, "fewer committed KECCAK columns than q_keccak has spare slots"
KECCAK_SLOT_OF = {KECCAK_IN + lane: lane for lane in range(STATE_LANES)} | {
    local: QKECCAK_SLOTS + spare for spare, local in enumerate(_KECCAK_COMMITTED[:QKECCAK_SPARE])
}


TABLES = (
    Table("xor", OP_XOR, ARITH_COLUMNS, _flushes_arith(OP_XOR, multiply=False)),
    Table("mul", OP_MUL, ARITH_COLUMNS, _flushes_arith(OP_MUL, multiply=True)),
    Table("set", OP_SET, SET_COLUMNS, _flushes_set()),
    Table("deref", OP_DEREF, DEREF_COLUMNS, _flushes_deref()),
    Table("jump", OP_JUMP, JUMP_COLUMNS, _flushes_jump(), _jump_constraints),
    Table("keccak", OP_KECCAK, KECCAK_COLUMNS, _flushes_keccak()),
)


TABLE_WIDTHS = tuple(t.width for t in TABLES)
GLOBAL_COLUMN_BASES = tuple(NUM_GLOBAL_COLUMNS + sum(TABLE_WIDTHS[:table]) for table in range(len(TABLES)))


TABLE_LOG_FLOORS = (0, 0, 0, 0, 0, KECCAK_MIN_STEPS_LOG)  # each table's least log height: 0, but the Keccak reduction's block of steps for KECCAK


def build_layout(bytecode: Sequence[K], log_memory: int, table_rows: Sequence[int]) -> Layout:
    log_bytecode = log2_strict(len(bytecode)) - BUS_BITS
    require(16 <= log_memory <= 32 and all(rows <= 2**32 for rows in table_rows) and 0 <= log_bytecode <= 32, "invalid announced table sizes")
    # A table's height is the least power of two holding its rows.
    table_log_heights = tuple(max(log2_ceil(rows), floor) for rows, floor in zip(table_rows, TABLE_LOG_FLOORS, strict=True))

    push: list[BusBlock] = []
    pull: list[BusBlock] = []
    count: list[BusBlock] = []
    for table, height, rows in zip(TABLES, table_log_heights, table_rows, strict=True):
        flushes = table.flushes
        for coordinates in flushes.push:
            push.append(BusBlock(height, rows, coordinates, table.opcode))
        for coordinates in flushes.pull:
            pull.append(BusBlock(height, rows, coordinates, table.opcode))
        for local in table.count_columns:
            count.append(BusBlock(height, rows, (_col(local),), table.opcode))

    # Every column's log size, in global order: the framework's, q_keccak's, then each table's block.
    qkeccak_kappa = table_log_heights[OP_KECCAK] + QKECCAK_SLOT_BITS
    kappas = [log_memory, log_memory, log_memory, log_memory, log_bytecode, qkeccak_kappa]
    for table in TABLES:
        kappas += [table_log_heights[table.opcode]] * table.width

    # A column q_keccak carries gets no block of its own: it IS one of its slots, 2^height words. An
    # output lane is not committed at all, nothing ever opening it.
    base = GLOBAL_COLUMN_BASES[OP_KECCAK]
    outputs = range(base + KECCAK_OUT, base + KECCAK_OUT + STATE_LANES)
    slots = {column: KECCAK_SLOT_OF.get(column - base) for column in range(len(kappas))}
    blocks = {column: kappa for column, kappa in enumerate(kappas) if slots[column] is None and column not in outputs}
    block_offsets, total_log = stack_offsets(list(blocks.values()))
    offsets = dict(zip(blocks, block_offsets))
    stack_log = max(MIN_STACKED_LOG, total_log)  # Floor at the PCS minimum

    def placement(column: int, kappa: int) -> Placement | None:
        if (slot := slots[column]) is not None:
            return Placement(kappa, offsets[QKECCAK] + (slot << kappa))
        return None if column in outputs else Placement(kappa, offsets[column])

    placements = [placement(column, kappa) for column, kappa in enumerate(kappas)]
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

WHIR_QUERIES = (((222,55), (223,56,30), (223,56,31), (223,56,32), (223,56,32), (223,56,32,22), (223,56,32,22), (224,56,32,23), (224,56,32,23), (224,56,32,23,17), (224,56,32,23,17), (224,56,32,23,18), (225,56,32,23,18), (225,56,32,23,18,14)), ((111,45), (112,45,27), (112,45,28), (112,45,28), (112,45,28), (112,45,28,20), (112,45,28,20), (112,45,28,21), (112,45,28,21), (112,45,28,21,16), (112,45,28,21,16), (112,45,28,21,16), (112,45,28,21,16), (112,45,28,21,16,13)), ((75,37), (75,37,24), (75,37,25), (75,38,25), (75,38,25), (75,38,25,18), (75,38,25,19), (75,38,25,19), (75,38,25,19), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15,13)), ((56,32), (56,32,22), (56,32,22), (56,32,23), (56,32,23), (56,32,23,17), (56,32,23,17), (56,32,23,18), (56,32,23,18), (56,32,23,18,14), (56,32,23,18,14), (56,32,23,18,14), (56,32,23,18,15), (56,32,23,18,15,12)))  # fmt: skip


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


# Keccak reduction ------------------------------------------------------------

KECCAK_RC = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
)  # fmt: skip
KECCAK_RHO = (0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14)
KECCAK_PI = tuple(i // 5 + 5 * ((2 * (i % 5) + 3 * (i // 5)) % 5) for i in range(STATE_LANES))  # where lane x + 5y lands


# Keccak, by GKR over its rounds ------------------------------------------------
#
# A claim is a weighted sum of the bits of one state per segment: (value, mu, point, weights),
# the weight of bit `j` of instance `i` of pack `y` in segment `m` being
# `eq(point, (y, m)) * weights[j] * mu[i]`. A pack is sixteen consecutive steps.

PACK_BITS = 4
EMBED_BITS = 24
PRODUCT_BITS = 2 * EMBED_BITS - 1
# The moduli the embedding is glued from, with the bits each holds.
RMFE_FACTORS = ((0b10, 1), (0b11, 1), (0b1011, 2), (0b1101, 2), (0b100101, 3), (0b101001, 3), (0b101111, 3))


def _carryless(a: int, b: int) -> int:
    out = 0
    while b:
        if b & 1:
            out ^= a
        a, b = a << 1, b >> 1
    return out


def _carryless_divmod(a: int, f: int) -> tuple[int, int]:
    quotient = 0
    while a and a.bit_length() >= f.bit_length():
        shift = a.bit_length() - f.bit_length()
        quotient |= 1 << shift
        a ^= f << shift
    return quotient, a


def _rmfe() -> tuple[list[int], list[int]]:
    """Sixteen bits embed in a binary polynomial of degree at most 23, and a product of two
    embeddings projects to the AND of what they embed. Returns each unit vector's embedding, and
    per bit of the projection the product coefficients it is the parity of."""
    modulus = reduce(_carryless, (f for f, _ in RMFE_FACTORS))
    embed, project = [], []
    for f, bits in RMFE_FACTORS:
        cofactor = _carryless_divmod(modulus, f)[0]
        degree = f.bit_length() - 1
        inverse = next(g for g in range(1, 2**degree) if _carryless_divmod(_carryless(_carryless_divmod(cofactor, f)[1], g), f)[1] == 1)
        lift = _carryless_divmod(_carryless(cofactor, inverse), modulus)[1]
        # A residue is the polynomial taking the bits as its values at 0, 1 and infinity.
        residues = {1: (1,), 2: (0b11, 0b10), 3: (0b011, 0b010, 0b110)}[bits]
        embed += [_carryless_divmod(_carryless(lift, r), modulus)[1] for r in residues]
        masks = [0] * bits
        for c in range(PRODUCT_BITS):
            g = _carryless_divmod(1 << c, f)[1]
            at_zero, at_one = g & 1, g.bit_count() & 1
            values = {1: (at_zero if f == 0b10 else at_one,), 2: (at_zero, at_one), 3: (at_zero, at_one, g >> 4)}[bits]
            for k, value in enumerate(values):
                masks[k] |= value << c
        project += masks
    # The last bit rides the leading coefficient, which the residues do not see.
    return [*embed, modulus], [*project, 1 << (PRODUCT_BITS - 1)]


RMFE_EMBED, RMFE_PROJECT = _rmfe()


@dataclass(frozen=True)
class KeccakClaim:
    value: E
    mu: Sequence[E]  # the weight of each instance of a pack
    point: MultilinearPoint  # a pack index, then a segment index
    weights: Sequence[E]  # the weight of each bit position


def keccak_along(j: int, k: int) -> int:
    """The position `k` columns along from `j`, in the same row and slice."""
    lane, z = divmod(j, 64)
    return 64 * ((lane % 5 + k) % 5 + 5 * (lane // 5)) + z


def keccak_linear_transpose(w: Sequence[E]) -> list[E]:
    """The transpose of theta, rho, pi on weight vectors: `<w, L(a)> = <L^T(w), a>`."""
    g = [ZERO] * KECCAK_BITS  # the weight each position of theta's output carries
    for lane in range(STATE_LANES):
        for z in range(64):
            g[64 * lane + z] = w[64 * KECCAK_PI[lane] + (z + KECCAK_RHO[lane]) % 64]
    columns = [E.sum(g[64 * (x + 5 * y) + z] for y in range(5)) for x in range(5) for z in range(64)]
    return [
        g[64 * lane + z] + columns[64 * ((lane % 5 + 1) % 5) + z] + columns[64 * ((lane % 5 + 4) % 5) + (z + 1) % 64]
        for lane in range(STATE_LANES)
        for z in range(64)
    ]


def keccak_instance_weights(s: E) -> list[E]:
    """The instance weights of a claim made at the polynomial point `s`: each unit vector's embedding at `s`."""
    s_powers = powers(s, EMBED_BITS)
    return [E.sum(s_powers[b] for b in range(EMBED_BITS) if e >> b & 1) for e in RMFE_EMBED]


def verify_keccak_layer(transcript: Transcript, log_steps: int, step: int, claim: KeccakClaim) -> KeccakClaim:
    """A claim on the states `step` layers below the committed outputs becomes one on the states a layer further down."""
    pack_bits = log_steps - PACK_BITS
    # 1] The product polynomial: the claim's weighted sum of the packs' unprojected chi.
    product = transcript.next_scalars(PRODUCT_BITS)
    projected = E.sum(E.sum(m for m, mask in zip(claim.mu, RMFE_PROJECT) if mask >> c & 1) * product[c] for c in range(PRODUCT_BITS))
    # iota flips known positions of lane 0 in every instance.
    segments = eq_kernel(claim.point[pack_bits:])
    iota = ZERO
    for segment in range(KECCAK_SEGMENTS):
        constant = KECCAK_RC[KECCAK_DEPTH * (segment + 1) - step - 1]
        iota += segments[segment] * E.sum(claim.weights[z] for z in range(64) if constant >> z & 1)
    require(projected + iota * E.sum(claim.mu) == claim.value, "Keccak product polynomial does not carry the claim")

    # 2] At a random point a pack is one field element, and the polynomial's value a sumcheck claim.
    s = transcript.sample()
    mu = keccak_instance_weights(s)
    kappa = E.sum(mu)
    value = poly_eval(product, s)

    # 3] The pack and the segment.
    scale = ONE
    point = []
    for r in claim.point:
        message = transcript.sumcheck_round_poly(3, value, r)
        challenge = transcript.sample()
        value = (ONE + r + challenge) * poly_eval(message, challenge)
        scale *= ONE + r + challenge
        point.append(challenge)

    # 4] The bit position: `sum_j w[j] (kappa T[j] + (kappa + T[j + 1]) T[j + 2])`, the weights one more multilinear factor.
    local, value = sumcheck(transcript, value, 4, [None] * KECCAK_LOCAL_BITS)
    t = transcript.next_scalars(3)
    eq = eq_kernel(local)
    require(
        scale * dot(eq[:KECCAK_BITS], claim.weights) * (kappa * t[0] + (kappa + t[1]) * t[2]) == value,
        "Keccak layer evaluations do not match the sumcheck",
    )

    # 5] `t[k] = sum_j eq[j] T[j + k]`: one claim on the state before chi, then on the round's input through the linear map.
    # Position `j` is `k` columns along from `keccak_along(j, 5 - k)`.
    beta = transcript.sample()
    weights = [eq[j] + beta * (eq[keccak_along(j, 4)] + beta * eq[keccak_along(j, 3)]) for j in range(KECCAK_BITS)]
    return KeccakClaim(t[0] + beta * (t[1] + beta * t[2]), mu, tuple(point), keccak_linear_transpose(weights))


def _keccak_open(transcript: Transcript, log_steps: int, claim: KeccakClaim, first: int, count: int, value: E) -> tuple[MultilinearPoint, list[E], E]:
    """A sumcheck over the slot: the point it ends on, the weight the claim puts on each slice there, and what is left
    to match. The claim weighs (slot, z) by its position weights, scaled by the segment, on the states it speaks of:
    `count` segments from `first`, the slots of every other column of the run weighing nothing."""
    slot, value = sumcheck(transcript, value, 3, [None] * QKECCAK_SLOT_BITS)
    segments = eq_kernel(claim.point[log_steps - PACK_BITS :])
    rows = [[ZERO] * 64 for _ in range(2**QKECCAK_SLOT_BITS)]
    for segment in range(count):
        for j in range(KECCAK_BITS):
            rows[STATE_LANES * (first + segment) + j // 64][j % 64] = segments[segment] * claim.weights[j]
    for challenge in slot:
        rows = [[lo + challenge * (lo + hi) for lo, hi in zip(rows[2 * i], rows[2 * i + 1], strict=True)] for i in range(len(rows) // 2)]
    return slot, rows[0], value


def verify_keccak(
    log_steps: int, instance: MultilinearPoint, output: Sequence[E], transcript: Transcript
) -> tuple[list[ColumnClaim], tuple[MultilinearPoint, list[E]]]:
    """The reduction: a random claim on every segment's output at `instance`, KECCAK_DEPTH layers down to the
    committed inputs. The last segment's output is the permutation's, claimed by the table's lanes `output` at
    `instance`; the others are committed. It leaves openings of q_keccak: the committed outputs as words at
    one point, and the column's 64 slices at another."""
    pack_bits = log_steps - PACK_BITS
    r_low = instance[:PACK_BITS]
    segment = transcript.samples(KECCAK_SEGMENT_BITS)
    point = (*instance[PACK_BITS:], *segment)
    # The first claim combines the output lanes as words: bit z of a word weighs x^z.
    lanes = eq_kernel(transcript.samples(KECCAK_LANE_BITS))
    weights = [lanes[j // 64] * E(1 << (j % 64)) for j in range(KECCAK_BITS)]
    last = eq_kernel(segment)[KECCAK_SEGMENTS - 1] * dot(lanes[:STATE_LANES], output)
    committed = transcript.next_scalar() if KECCAK_SEGMENTS > 1 else ZERO
    first = KeccakClaim(committed + last, eq_kernel(r_low), point, weights)
    claim = first
    for step in range(KECCAK_DEPTH):
        claim = verify_keccak_layer(transcript, log_steps, step, claim)

    # The committed outputs, whose instance weights are an eq already: slice 0 holds the slot's weight, the others x^z times it.
    outputs = []
    if KECCAK_SEGMENTS > 1:
        slot, weights, value = _keccak_open(transcript, log_steps, first, 1, KECCAK_SEGMENTS - 1, committed)
        word = transcript.next_scalar()
        require(weights[0] * word == value, "Keccak output opening ends on the wrong value")
        outputs.append(ColumnClaim(QKECCAK, (*r_low, *instance[PACK_BITS:], *slot), word))
    # The inputs: the instances of a pack first, then the slot.
    low, value = sumcheck(transcript, claim.value, 3, [None] * PACK_BITS)
    slot, weights, value = _keccak_open(transcript, log_steps, claim, 0, KECCAK_SEGMENTS, value)
    slices = transcript.next_scalars(K_BITS)
    require(multilinear_eval(claim.mu, low) * dot(weights, slices) == value, "Keccak input opening ends on the wrong value")
    return outputs, ((*low, *claim.point[:pack_bits], *slot), slices)


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
    """The 64 claims s[i] = z(i, point) become the one dense claim `sum_u W(u) qkeccak(u) = target`.

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
    bytecode_hash = keccak_hash(b"".join(word.to_bytes() for word in bytecode))
    relation = keccak_hash(RELATION_LABEL).value
    iv_preimage = b"leanvm" + pack("<Q", len(relation)) + relation + bytecode_hash.value
    fiat_shamir_IV = keccak_hash(iv_preimage)
    transcript = Transcript(proof, fiat_shamir_IV, public_input)

    # 1] memory log-size, table row counts, and log-inv-rate in WHIR
    announced = transcript.next_scalars(2 + len(TABLES))
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced size has a nonzero high limb")
    log_memory = int(announced[0].c0)
    table_rows = tuple(int(value.c0) for value in announced[1 : 1 + len(TABLES)])
    log_inverse_rate = int(announced[-1].c0)
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    layout = build_layout(bytecode, log_memory, table_rows)
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
    evaluations = table_sumcheck(layout.table_log_heights, bus.forms, constraint_powers, form_powers, bus.point, target, transcript)
    claims = list(bus.claims)
    for base, (point, values) in zip(GLOBAL_COLUMN_BASES, evaluations, strict=True):
        claims.extend(ColumnClaim(base + local, point, value) for local, value in enumerate(values))

    # 5] binding the public input: each memory limb's claim is that limb's public line at the challenge, which the verifier
    # evaluates itself, so the prover sends nothing. Both public words are 128-bit, so the top limb's claim is zero.
    public_challenge = transcript.sample()
    first, second = public_input.halves()
    public_limbs = tuple(multilinear_eval(pair, [public_challenge]) for pair in ((first.c0, second.c0), (first.c1, second.c1), (first.c2, second.c2)))
    public_point = (public_challenge, *[ZERO] * (layout.placements[MEMORY_0].variables - 1))
    claims.extend(ColumnClaim(column, public_point, value) for column, value in zip((MEMORY_0, MEMORY_1, MEMORY_2), public_limbs))

    # 6] KECCAK validity, by GKR over the rounds. The table's claims on its output lanes are the reduction's claim on
    # the permutation's output: they leave the batch, their columns having no placement.
    point, values = evaluations[OP_KECCAK]
    outputs, (point, slices) = verify_keccak(layout.table_log_heights[OP_KECCAK], point, values[KECCAK_OUT : KECCAK_OUT + STATE_LANES], transcript)
    claims.extend(outputs)

    # 7] Ring-switching
    # That claim is supported on q_keccak's region of the stack, so its weight carries the
    # placement's selector, and it leads the batch, taking the first power.
    target, weight = ring_switch(point, slices, transcript)
    qkeccak = layout.placements[QKECCAK]
    ringswitch = (lambda x: qkeccak.eq_above(x) * weight(x[: qkeccak.variables]), target)
    stack_claims = (c.on_stack(layout) for c in claims)
    verify_stacked_opening(transcript, root, layout.stack_log, log_inverse_rate, [ringswitch, *(c for c in stack_claims if c is not None)])
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
