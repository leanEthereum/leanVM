# expect: ok
# public_input: 17, 17
# Builds a chain of three unwritten cells joined only by DEREF links, then writes the far end with an assert: the
# value must spread back along every link so a runtime-pointer read of the first cell sees it.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    a = hb[1]
    hb[GEN] = a
    c = hb[GEN]
    hb[GEN ** 2] = c
    d = hb[GEN ** 2]
    assert 17 == d
    i = GEN ** 0
    p = GEN ** 0
    p[1] = hb[i]
    p[GEN] = a
    return
