# Import this in zkDSL .py files to make them executable as normal Python

import math
from typing import Any

# Type annotations
Mut = Any
Const = Any
Imm = Any


# @inline decorator (does nothing in Python execution)
def inline(fn):
    return fn


def unroll(a: int, b: int):
    return range(a, b)


def parallel_range(a: int, b: int):
    return range(a, b)


# Array - simulates write-once memory with pointer arithmetic
class Array:
    def __init__(self, size: int):
        # TODO
        return

    def __getitem__(self, idx):
        # TODO
        return

    def __setitem__(self, idx, value):
        # TODO
        return

    def __add__(self, offset: int):
        # TODO
        return

    def __len__(self):
        # TODO
        return


# Poseidon16 precompiles on input x = m[left..left+8] || m[right..right+8], written at `output`:
#   - `compress_*` adds the input back, i.e. feed-forward (Poseidon(x) + x); `permute_*` is the raw Poseidon(x).
#   - `_half` keeps 8 elements, `_quarter` keeps 4, plain `permute` keeps 16
#   - `_hardcoded_left`: the left half is m[offset..offset+4] || m[left..left+4], at the compile-time constant `offset`.


def poseidon16_compress_half(left, right, output):
    """m[output..output+8] = (Poseidon(x) + x)[0..8]."""
    _ = left, right, output


def poseidon16_compress_quarter(left, right, output):
    """m[output..output+4] = (Poseidon(x) + x)[0..4]."""
    _ = left, right, output


def poseidon16_compress_half_hardcoded_left(left, right, output, offset):
    """`poseidon16_compress_half` with a hardcoded left prefix: the left half of the input is
    m[offset..offset+4] || m[left..left+4]."""
    _ = left, right, output, offset


def poseidon16_compress_quarter_hardcoded_left(left, right, output, offset):
    """`poseidon16_compress_quarter` with a hardcoded left prefix: the left half of the input is
    m[offset..offset+4] || m[left..left+4]."""
    _ = left, right, output, offset


def poseidon16_permute(left, right, output):
    """m[output..output+16] = Poseidon(x) (raw permutation, no feed-forward)."""
    _ = left, right, output


def poseidon16_permute_half(left, right, output):
    """m[output..output+8] = Poseidon(x)[0..8] (raw permutation, no feed-forward; high 8 discarded)."""
    _ = left, right, output


def poseidon16_permute_half_hardcoded_left(left, right, output, offset):
    """`poseidon16_permute_half` with a hardcoded left prefix: the left half of the input is
    m[offset..offset+4] || m[left..left+4]."""
    _ = left, right, output, offset


def add_be(a, b, result, length=None):
    _ = a, b, result, length


def add_ee(a, b, result, length=None):
    _ = a, b, result, length


def dot_product_be(a, b, result, length=None):
    _ = a, b, result, length


def dot_product_ee(a, b, result, length=None):
    _ = a, b, result, length


def poly_eq_be(a, b, result, length=None):
    _ = a, b, result, length


def poly_eq_ee(a, b, result, length=None):
    _ = a, b, result, length


def hint_decompose_bits(value, bits, n_bits):
    _ = value, bits, n_bits


def hint_less_than(a, b, result_ptr):
    _ = a, b, result_ptr


def log2_ceil(x: int) -> int:
    assert x > 0
    return math.ceil(math.log2(x))


def div_ceil(a: int, b: int) -> int:
    return (a + b - 1) // b


def div_floor(a: int, b: int) -> int:
    return a // b


def next_multiple_of(x: int, n: int) -> int:
    return x + (n - x % n) % n


def saturating_sub(a: int, b: int) -> int:
    return max(0, a - b)


def debug_assert(cond, msg=None):
    if not cond:
        if msg:
            raise AssertionError(msg)
        raise AssertionError()


def match_range(value: int, *args):
    """Match a value against multiple continuous ranges with different lambdas.

    Usage: match_range(value, range(a,b), lambda1, range(b,c), lambda2, ...)
    In zkDSL, this expands to a match statement.
    In Python execution, it finds the matching range and calls the corresponding lambda.
    """
    for i in range(0, len(args), 2):
        rng = args[i]
        fn = args[i + 1]
        if value in rng:
            return fn(value)
    raise AssertionError(f"Value {value} not in any range")


def hint_decompose_bits_xmss(*args):
    _ = args


def hint_decompose_bits_merkle_whir(*args):
    _ = args


def hint_log2_ceil(n):
    return log2_ceil(n)


def hint_div_floor(a, b, q_ptr, r_ptr):
    _ = a, b, q_ptr, r_ptr


def hint_witness(name, destination):
    """Write the next witness entry for `name` into `destination`."""
    _ = (name, destination)
