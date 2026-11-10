# expect: compile-error out of bounds
# A compile-time heap index equal to the buffer size: the compiler bounds-checks compile-time indices and must refuse
# it, since the cell belongs to the next allocation.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    hb[GEN ** 4] = 1
    return
