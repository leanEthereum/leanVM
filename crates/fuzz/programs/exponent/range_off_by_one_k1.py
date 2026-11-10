# expect: exec-fail not a small g-power
# x = g^1 against the bound 1: one past the largest accepted exponent. The complement's DEREF must fail, or the
# range check admits an element it exists to exclude.
from snark_lib import *


def main():
    hb = HeapBuf(1)
    hb[1] = GEN
    assert log(hb[1]) < 1
    return
