# expect: exec-fail write-once conflict
# public_input: 0, 0
# assert a == b on words that differ only in their third limb: the equality must compare all 192 bits.
from snark_lib import *


def main():
    hb = HeapBuf(2)
    hb[1] = f192(5, 6, 0)
    hb[GEN] = f192(5, 6, 7)
    assert hb[1] == hb[GEN]
    return
