# expect: ok
# public_input: 9, 0
# A heap cell stored twice with one value, through two spellings of its address: the second store must be a no-op
# equality, not a conflict, or every write-once assertion idiom breaks.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    hb[GEN] = 9
    view = hb * GEN
    view[1] = 9
    i = GEN * 1
    hb[i] = 9
    p = GEN ** 0
    p[1] = hb[GEN]
    return
