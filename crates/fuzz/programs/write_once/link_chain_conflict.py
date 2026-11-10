# expect: exec-fail write-once conflict
# public_input: 17, 0
# The same DEREF-linked chain, written with 17 at one end and then with 18 at the other: the spread value must make
# the second write a conflict, not let two linked names hold different words.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    a = hb[1]
    hb[GEN] = a
    c = hb[GEN]
    hb[GEN ** 2] = c
    d = hb[GEN ** 2]
    assert 17 == d
    p = GEN ** 0
    p[1] = d
    i = GEN ** 0
    hb[i] = 18
    return
