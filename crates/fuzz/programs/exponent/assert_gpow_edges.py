# expect: ok
# public_input: GEN ** 60000, 0
# `assert_gpow` is a lone DEREF: it accepts g^0 and an exponent near the minimum memory size, and nothing else is
# checked. The far element must not be mistaken for a wild pointer.
from snark_lib import *


def main():
    a = GEN ** 0
    b = GEN ** 60000
    hb = HeapBuf(2)
    hb[1] = a
    hb[GEN] = b
    assert_gpow(hb[1])
    assert_gpow(hb[GEN])
    p = GEN ** 0
    p[1] = hb[GEN]
    return
