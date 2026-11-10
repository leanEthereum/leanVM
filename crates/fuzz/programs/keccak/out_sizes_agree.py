# expect: ok
# public_input: 76870798587041994854595358325668108629, 156543651484862875866541738639399140452
# One message hashed into a 1-cell, a 2-cell and a 13-cell out, the last on the heap: each writes the first cells of
# one state, so they must agree cell for cell, and the 2-cell digest is pinned from an independent Keccak-256.
from snark_lib import *


def main():
    m = [242716439218147592190247776532461068291, 178663287798046340062194692478498369747, 114610156739272160164435410271743099043, 50562197615718748928369898115721695347]
    o1 = StackBuf(1)
    keccak(m[0:2], m[2:4], o1)
    o2 = StackBuf(2)
    keccak(m[0:2], m[2:4], o2)
    hb = HeapBuf(13)
    keccak(m[0:2], m[2:4], hb[0:13])
    o13 = StackBuf(13)
    keccak(m[0:2], m[2:4], o13)
    assert o1[0] == o2[0]
    assert o2[1] == hb[GEN]
    assert o13[12] == hb[GEN ** 12]
    assert o13[8] == hb[GEN ** 8]
    assert o2[0] == 76870798587041994854595358325668108629
    assert o2[1] == 156543651484862875866541738639399140452
    p = GEN ** 0
    p[1] = hb[1]
    p[GEN] = o13[1]
    return
