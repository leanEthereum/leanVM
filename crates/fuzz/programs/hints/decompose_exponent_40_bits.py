# expect: ok
# The widest exponent decomposition the compiler allows: 40 bits of g^1000003, whose bits the program checks, and a
# booleanity pin on every hinted bit since the hint itself is unconstrained.
from snark_lib import *


def main():
    bits = StackBuf(40)
    hint_decompose_bits_exponent(bits, GEN ** 1000003, 40)
    for i in unroll(0, 40):
        assert bits[i] == bits[i] * bits[i]
    assert bits[0] == 1
    assert bits[1] == 1
    assert bits[2] == 0
    assert bits[39] == 0
    p = GEN ** 0
    p[1] = bits[0] + bits[6]
    return
