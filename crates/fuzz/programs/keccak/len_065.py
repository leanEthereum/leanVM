# expect: ok
# public_input: 68743791033394745441520224336789118983, 45663353797178399725045442677244111760
# keccak with a tail operand at len=65: the message spans a, b and part of tail, and the padding lands
# inside the tail. The digest is pre-written from an independent Keccak-256, so a misplaced padding byte or a
# cell dropped from the tail conflicts.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    hb[GEN ** 0] = 71871383284339455167932608602839527435
    hb[GEN ** 1] = 178621423072424560128051388010014802011
    hb[GEN ** 2] = 285376675360240156043455777163709894827
    hb[GEN ** 3] = 50520332810868806498481338092594995451
    hb[GEN ** 4] = 75
    out = StackBuf(2)
    out[0] = 68743791033394745441520224336789118983
    out[1] = 45663353797178399725045442677244111760
    keccak([hb[GEN ** 0], hb[GEN ** 1]], [hb[GEN ** 2], hb[GEN ** 3]], out, tail=[hb[GEN ** 4], 0, 0, 0], len=65)
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
