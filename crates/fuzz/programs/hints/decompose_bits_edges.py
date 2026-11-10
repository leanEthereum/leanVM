# expect: ok
# public_input: 18446744073709551615, 1
# hint_decompose_bits at nbits 0, 1, 63 and 64, on 0, 1, a value with bit 63 set and the all-ones limb: each bit is
# pinned boolean and recomposed as a polynomial in g = x, so a dropped, doubled or misplaced bit conflicts.
from snark_lib import *


@inline
def pin_bits(bits, v, n: Const):
    acc = 0
    for i in unroll(0, n):
        assert bits[i] * bits[i] == bits[i]
        acc = acc + bits[i] * GEN ** i
    assert acc == v
    return acc


def main():
    b0 = StackBuf(1)
    hint_decompose_bits(b0, 0, 0)
    b1 = StackBuf(1)
    hint_decompose_bits(b1, 1, 1)
    one = pin_bits(b1, 1, 1)
    b63 = StackBuf(63)
    v63 = 9223372036854775807
    hint_decompose_bits(b63, v63, 63)
    t63 = pin_bits(b63, v63, 63)
    b64 = StackBuf(64)
    v64 = 18446744073709551615
    hint_decompose_bits(b64, v64, 64)
    top = pin_bits(b64, v64, 64)
    z = StackBuf(64)
    hint_decompose_bits(z, 0, 64)
    t0 = pin_bits(z, 0, 64)
    p = GEN ** 0
    p[1] = top
    p[GEN] = one
    return
