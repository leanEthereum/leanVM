# expect: ok
# public_input: 11132226378611961298753850763813414096, 214055521708877375168425834874734729162
# keccak at len=32: the padding byte lands at byte 32 of the 64-byte operand pair, and every cell wholly past the
# message is a literal zero. The digest is pre-written from an independent Keccak-256, so any misplaced padding conflicts.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    hb[GEN ** 0] = 71871383284339455167932608602839527435
    hb[GEN ** 1] = 178621423072424560128051388010014802011
    out = StackBuf(2)
    out[0] = 11132226378611961298753850763813414096
    out[1] = 214055521708877375168425834874734729162
    keccak([hb[GEN ** 0], hb[GEN ** 1]], [0, 0], out, len=32)
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
