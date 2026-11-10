# expect: ok
# A constant heap index that equals g^k names cell k however it is spelled: GEN ** 6, (GEN ** 2) ** 3, a name bound to
# it, and a product of g-powers must all reach the same cell, which the write-once memory then checks for agreement.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    hb[(GEN ** 2) ** 3] = 5
    assert hb[GEN ** 6] == 5
    x = (GEN ** 2) ** 3
    assert hb[x] == 5
    hb[GEN ** 2 * GEN ** 4] = 5
    hb[GEN * GEN] = 7
    assert hb[GEN ** 2] == 7
    p = GEN ** 0
    p[1] = hb[x] * hb[GEN ** 2]
    return
