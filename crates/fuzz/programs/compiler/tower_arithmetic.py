# expect: ok
# public_input: 2 + 5 * 18446744073709551616, 0
# GF(2^128) tower identities on full-width words: y^2 = xy + 1 (low limb 1, high limb x = 2), and each further
# power folded by the modulus, checked with runtime MULs.
from snark_lib import *

def main():
    hb = HeapBuf(3)
    hb[1] = 18446744073709551616
    hb[GEN] = 1 + 2 * 18446744073709551616
    y = hb[1]
    y2 = hb[GEN]
    assert y * y == y2
    assert y2 * y == 2 + 5 * 18446744073709551616
    assert y2 * y2 == 5 + 8 * 18446744073709551616
    inv = 1 / y
    assert inv * y == 1
    p = GEN ** 0
    p[1] = y2 * y
    return
