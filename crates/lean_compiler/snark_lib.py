# Import this in zkDSL .py files (`from snark_lib import *`) so editors and
# linters resolve the builtins. The compiler skips the import; it does not
# include other source files (single-file programs only). Resolved through
# `extraPaths` in the root pyrightconfig.json; see zkDSL.md. A guest is not a
# runnable Python file: its `*_PLACEHOLDER` names are filled in at compile time,
# so `import`ing one raises NameError.

from typing import Any, Optional

Const = Any
"""Parameter annotation: `def f(k: Const, x):`, where `k` is a compile-time
argument; the compiler specializes the function per distinct constant."""


class _Elt:
    """A 192-bit machine word in E = GF(2^192), represented as a cubic tower
    over K = GF(2^64). Indices and addresses are K-valued powers of GEN, i.e.
    "in the exponent": `GEN ** k` is the k-th index and `x * GEN` its successor.
    A heap pointer is K-valued too; `buf[i]` is the write-once cell at `buf * i`."""

    def __add__(self, other):  # field addition = XOR
        _ = other
        return _Elt()

    __radd__ = __add__

    def __mul__(self, other):  # tower-field product
        _ = other
        return _Elt()

    __rmul__ = __mul__

    def __truediv__(self, other):  # field division a / b = a · b⁻¹ (single slash)
        _ = other
        return _Elt()

    __rtruediv__ = __truediv__

    def __pow__(self, k: int):
        _ = k
        return _Elt()

    def __getitem__(self, idx):  # heap read m[self · idx]
        _ = idx
        return _Elt()

    def __setitem__(self, idx, value):  # heap store m[self · idx] (write-once)
        _ = idx, value


def f192(c0: int, c1: int, c2: int) -> _Elt:
    """Construct a field constant from its three little-endian GF(2^64) limbs."""
    _ = c0, c1, c2
    return _Elt()


GEN = _Elt()
"""The fixed generator g = x of K^× = GF(2^64)^× (order 2^64 - 1)."""


def hint_decompose_bits(bits, value, nbits: int) -> None:
    """Computed advice: the prover writes the `nbits` bits of `value` into the
    `bits` buffer. UNCONSTRAINED: the caller must check booleanity and that the
    bits reconstruct `value` (a range check that `value < 2^nbits`)."""
    _ = bits, value, nbits


def hint_decompose_bits_exponent(bits, x, nbits: int) -> None:
    """Computed advice: the prover writes the `nbits` bits of n, where x = g^n
    (recovered by a bounded discrete log at witness generation), into `bits`.
    UNCONSTRAINED: the caller checks booleanity and Π g^(bit_j 2^j) == x."""
    _ = bits, x, nbits


def hint_log2_ceil(bits, nbits: int, floor: int) -> _Elt:
    """Computed advice: returns `g^max(log2_ceil(v), floor)`, where `v` is the
    integer the `nbits`-cell `bits` buffer decodes to. The prover fills it at
    witness-generation; it is UNCONSTRAINED, so the caller must verify it (see the
    log2_ceil_in_the_exponent wrapper in the recursion guest). log2 = base-2 log of the integer, NOT the
    discrete log base g that `log(...)` means."""
    _ = bits, nbits, floor
    return _Elt()


def const(e):
    """`if const(a == b):` asks for the branch to be decided while compiling, and
    `const(e)` in a value position asks for `e` itself to be read that way.

    Two things follow. The condition must be decidable then (both sides
    compile-time integers), and it is read with INTEGER arithmetic, which is the
    regime a compile-time constant lives in. Without the wrapper, a condition
    whose integer and field readings disagree is rejected rather than silently
    decided one way, since `+` is XOR in a value. A folded branch is
    straight-line code, so unlike a runtime branch its bindings outlive it."""
    return e


def log(x) -> int:
    """The discrete log base GEN: `x = GEN ** log(x)`. Only meaningful inside
    a range-check assert (`assert log(x) < log(GEN ** k)`, equivalently
    `assert log(x) < k`, proves `x ∈ {GEN**0, …, GEN**(k-1)}` in 3 cycles),
    or as the scrutinee of `match`."""
    _ = x
    return 0

# @inline decorator (does nothing in Python execution)
def inline(fn):
    return fn


def match(value: int, *args):
    """A `match` with generated arms: `match(log(x), range(a, b),
    lambda i: …, …)` expands to one arm per integer of the contiguous ranges
    (which must start at 0), the lambda applied to the concrete value; the
    results bind to the assignment targets. In Python execution, finds the
    matching range and calls its lambda."""
    for i in range(0, len(args), 2):
        rng, fn = args[i], args[i + 1]
        if value in rng:
            return fn(value)
    raise AssertionError(f"value {value} not in any range")


def mul_range(start, stop) -> list:
    """The loop counter walked in the exponent: from element `start` to `stop`
    (exclusive), ×GEN each iteration. `start` is a compile-time power of GEN
    (`1`, `GEN`, or `GEN ** k`); `stop` is one too, or else a runtime g-power
    element the walk must be able to reach."""
    _ = start, stop
    return []


def unroll(a: int, b: int) -> range:
    """Compile-time unrolling: the body is replicated for i = a, …, b-1, the
    counter substituted as an integer literal (usable as a stack index, slice
    bound, or `Const` argument). Bounds are compile-time integers, including
    `Const` parameters."""
    return range(a, b)


def HeapBuf(n) -> _Elt:
    """Allocate a fresh, disjoint heap buffer; evaluates to its pointer (a
    fresh g-power). `n` is either an integer literal (compile-time size), or a
    runtime value carrying the cell count *in the exponent*: `g^k` allocates
    `k` cells, so a size derived from a g-power count is plain field arithmetic
    (`HeapBuf(cnt * cnt)` is `2·log(cnt)` cells). Allocation is a prover
    convenience, so an under-size only trips write-once."""
    _ = n
    return _Elt()


def StackBuf(n: int) -> _Elt:
    """Allocate `n` consecutive frame (stack) cells. A size-2 StackBuf holds a
    256-bit value and is a valid `blake2s` operand."""
    _ = n
    return _Elt()


def addr(buf) -> _Elt:
    """The g-address of a StackBuf's first cell, so a frame run can be pointed
    at: `p = addr(sb)` binds a pointer whose `p[i]` / `p * GEN ** k` behave like
    a HeapBuf's, while `sb[k]` itself stays a direct frame cell. Costs one
    materialization of `fp` per function (2 DEREFs, amortized; free in `main`).
    Only valid as the whole right-hand side of an assignment."""
    _ = buf
    return _Elt()


def hint_witness(dest, name: Optional[str] = None) -> Any:
    """Take the next ENTRY (a slice of values) of the named prover witness
    stream.

    Two forms. As a statement, `hint_witness(dest, "name")` fills `dest` (a
    StackBuf, or a StackBuf/HeapBuf slice of any length). As an expression,
    `x = hint_witness("name")` binds ONE value and needs no destination, the
    entry then having to hold exactly one value.

    The same symbol may be hinted many times, each call popping the next entry
    (`Program::set_witness`; test programs declare one `# witness name: v1, …`
    line per entry). Zero cycles either way, and the values are completely
    UNCONSTRAINED: the program must constrain them itself (asserts, range
    checks, hashes)."""
    _ = dest, name
    return _Elt()


def assert_in_k(a, b) -> None:
    """Prove that both machine words are GF(2^64)-valued. This is the sole
    packing-related intrinsic and lowers to one untaken JUMP."""
    _ = a, b


def hint_f192_limbs(dest, value) -> None:
    """Computed advice: write the first `len(dest)` GF(2^64) coordinate limbs
    of `value` into a 1-to-3-cell StackBuf. UNCONSTRAINED; callers bind the
    result with `assert_in_k` and field reconstruction."""
    _ = dest, value


def blake2s(
    a,
    b,
    out,
    *,
    cv=None,
    counter: Optional[int] = None,
    final: Optional[int] = None,
    last_node: int = 0,
    md=None,
) -> None:
    """One standard BLAKE2s compression of the two 256-bit message operands
    `a`, `b`, written into the 2-cell run `out` (write-once: if `out` was
    already written, this asserts it equals the chaining value).

    With no keywords this hashes exactly 64 bytes: the parameterized BLAKE2s-256
    initial chaining value, byte counter 64, final-block flag set. That is
    `blake2s(a || b)`, the form every Fiat-Shamir step and Merkle node uses.

    For a longer message, drive the blocks yourself. `counter` is the CUMULATIVE
    byte count through this block (`64 * whole_blocks_before + bytes_in_this_block`)
    and `final=1` marks the last block; `cv` carries the previous block's output
    and requires one of `counter`, `final`, `last_node` or `md`. Setting any of
    `counter`, `final` or `last_node` makes `final` default
    to 0, so a single short block needs `counter=<len>, final=1`. Bytes past the
    block's real length must be zero-filled by the program. `last_node` is
    BLAKE2s's tree-mode `f1` and is 0 everywhere here.

    `md` is the whole 128-bit metadata word as a value the program computed, for
    a hash whose block count is only known at run time. It replaces `counter`,
    `final` and `last_node` (giving both is an error), and it must not name a
    cell of `out`.

    Message, chaining-value, and output operands are size-2 StackBufs or
    2-cell slices `buf[lo:hi]` of larger StackBufs or HeapBufs (heap inputs are
    bridged through the stack, one DEREF per cell)."""
    _ = a, b, out, cv, counter, final, last_node, md
