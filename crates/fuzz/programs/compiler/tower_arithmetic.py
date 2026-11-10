# expect: ok
# public_input: 18446744073709551616 + 1, 0
# GF(2^192) tower identities on full-width words: y^3 = y + 1 and y^4 = y^2 + y, built with f192 literals
# and checked with runtime MULs.
from snark_lib import *

def main():
    hb = HeapBuf(3)
    hb[1] = f192(0, 1, 0)
    hb[GEN] = f192(0, 0, 1)
    y = hb[1]
    y2 = hb[GEN]
    assert y * y == y2
    assert y2 * y == f192(1, 1, 0)
    assert y2 * y2 == f192(0, 1, 1)
    inv = 1 / y
    assert inv * y == 1
    p = GEN ** 0
    p[1] = y2 * y
    return
