# expect: ok
# public_input: 1, 1
# Raises runtime K elements to 2^64 - 1, the order of K^x, by square-and-multiply in two compile-time exponents
# (a^(2^32-1) then that to 2^32 + 1): the result is one for any nonzero K element, and y^(2^128) is not one.
from snark_lib import *


def main():
    hb = HeapBuf(2)
    hb[1] = GEN ** 12345
    hb[GEN] = 5
    a = hb[1] ** 4294967295
    a2 = a ** 2147483648
    b = hb[GEN] ** 4294967295
    b2 = b ** 2147483648
    assert a2 * a2 * a == 1
    assert b2 * b2 * b == 1
    assert a != 1
    y = 18446744073709551616
    c = y ** 4294967295
    d = c ** 4294967295
    assert d * c * y != 1
    p = GEN ** 0
    p[1] = a2 * a2 * a
    p[GEN] = b2 * b2 * b
    return
