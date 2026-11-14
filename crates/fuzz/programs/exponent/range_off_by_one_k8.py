# expect: exec-fail not a g-power below 2^28
# x = g^8 against the bound 8: one past the largest accepted exponent. The complement's DEREF must fail, or the
# range check admits an element it exists to exclude.
from snark_lib import *


def main():
    hb = HeapBuf(1)
    hb[1] = GEN ** 8
    assert log(hb[1]) < 8
    return
