# expect: ok
# public_input: 216048828569474662557787918230376202578, 278601662843772356939973603907190468112
# keccak at len=64: the padding byte lands at byte 64 of the 64-byte operand pair, and every cell wholly past the
# message is a literal zero. The digest is pre-written from an independent Keccak-256, so any misplaced padding conflicts.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    hb[GEN ** 0] = 71871383284339455167932608602839527435
    hb[GEN ** 1] = 178621423072424560128051388010014802011
    hb[GEN ** 2] = 285376675360240156043455777163709894827
    hb[GEN ** 3] = 50520332810868806498481338092594995451
    out = StackBuf(2)
    out[0] = 216048828569474662557787918230376202578
    out[1] = 278601662843772356939973603907190468112
    keccak([hb[GEN ** 0], hb[GEN ** 1]], [hb[GEN ** 2], hb[GEN ** 3]], out, len=64)
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
