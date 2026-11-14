# expect: exec-fail not a g-power below 2^28
# witness i: 18446744073709551616
# A heap read at the runtime index y (the tower element, outside K): the pointer has a nonzero middle limb, so it is
# no address, and the DEREF must refuse it instead of reading its low limb.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    hb[1] = 3
    i = hint_witness("i")
    v = hb[i]
    p = GEN ** 0
    p[1] = v
    return
