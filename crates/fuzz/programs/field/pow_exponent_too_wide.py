# expect: compile-error does not fit in 32 bits
# A field power whose compile-time exponent is 2^32 does not fit the compiler's exponent type: it must be refused at
# compile time, not truncated to x^0 = 1.
from snark_lib import *


def main():
    hb = HeapBuf(1)
    hb[1] = GEN ** 3
    a = hb[1] ** 4294967296
    p = GEN ** 0
    p[1] = a
    return
