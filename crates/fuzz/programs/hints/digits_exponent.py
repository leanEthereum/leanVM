# expect: ok
# public_input: GEN ** 9, GEN ** 10
# hint_decompose_digits_exponent: x = g^0xA9B (2715) as three 4-bit digits from bit 0, and from a runtime start g^4.
# Each digit arrives as g^d; they are range-checked and recombined, so a digit from the wrong offset conflicts.
from snark_lib import *


def main():
    x = GEN ** 2715
    d = StackBuf(3)
    hint_decompose_digits_exponent(d, x, 12, 3, 4, 0)
    assert log(d[0]) < 16
    assert log(d[1]) < 16
    assert log(d[2]) < 16
    assert d[0] == GEN ** 11
    assert d[1] == GEN ** 9
    assert d[2] == GEN ** 10
    e = StackBuf(2)
    s = GEN ** 4
    hint_decompose_digits_exponent(e, x, 12, 2, 4, s)
    assert e[0] == d[1]
    assert e[1] == d[2]
    p = GEN ** 0
    p[1] = e[0]
    p[GEN] = e[1]
    return
