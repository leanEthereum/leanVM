# expect: exec-fail write-once conflict
# public_input: 0, 0
# assert a == b on words that differ only in their high limb: the equality must compare all 128 bits.
from snark_lib import *


def main():
    hb = HeapBuf(2)
    hb[1] = 5
    hb[GEN] = 5 + 18446744073709551616
    assert hb[1] == hb[GEN]
    return
