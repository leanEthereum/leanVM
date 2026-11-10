# expect: ok
# public_input: GEN ** 40000, GEN ** 7
# hint_decompose_bits_exponent at nbits 1 (x = g^0 and g^1), at 3 for the top value 7, and at 16 for 40000: the bits
# are pinned boolean and the exponent rebuilt as a product of g^(2^i) factors, so a wrong bit conflicts.
from snark_lib import *


@inline
def rebuild(bits, n: Const):
    acc = 1
    for i in unroll(0, n):
        assert bits[i] * bits[i] == bits[i]
        acc = acc * (1 + bits[i] * (GEN ** (2 ** i) + 1))
    return acc


def main():
    a = StackBuf(1)
    hint_decompose_bits_exponent(a, GEN ** 0, 1)
    assert rebuild(a, 1) == 1
    b = StackBuf(1)
    hint_decompose_bits_exponent(b, GEN, 1)
    assert rebuild(b, 1) == GEN
    c = StackBuf(3)
    hint_decompose_bits_exponent(c, GEN ** 7, 3)
    r7 = rebuild(c, 3)
    d = StackBuf(16)
    hint_decompose_bits_exponent(d, GEN ** 40000, 16)
    r = rebuild(d, 16)
    p = GEN ** 0
    p[1] = r
    p[GEN] = r7
    return
