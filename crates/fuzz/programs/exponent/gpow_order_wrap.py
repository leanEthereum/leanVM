# expect: ok
# public_input: GEN, 1
# g-power arithmetic that wraps the order 2^64 - 1 of g, built from u32 exponents at runtime: g^(2^32-1) raised to
# 2^32 + 1 is g^0 = 1, and a pointer equal to buf * 1 reached that way must address cell 0 of the buffer.
from snark_lib import *


def main():
    hb = HeapBuf(2)
    hb[1] = GEN ** 4294967295
    a = hb[1]
    b = a ** 2147483648
    one = b * b * a
    assert one == 1
    buf = HeapBuf(2)
    buf[1] = GEN
    v = buf[one]
    p = GEN ** 0
    p[1] = v
    p[GEN] = one
    return
