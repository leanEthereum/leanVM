# expect: ok
# public_input: 136558582153236824742329488191936919940, 263903983233857944230612641983592219616
# keccak at len=63: the padding byte lands at byte 63 of the 64-byte operand pair, and every cell wholly past the
# message is a literal zero. The digest is pre-written from an independent Keccak-256, so any misplaced padding conflicts.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    hb[GEN ** 0] = 71871383284339455167932608602839527435
    hb[GEN ** 1] = 178621423072424560128051388010014802011
    hb[GEN ** 2] = 285376675360240156043455777163709894827
    hb[GEN ** 3] = 9668971042003328136669801941901563
    out = StackBuf(2)
    out[0] = 136558582153236824742329488191936919940
    out[1] = 263903983233857944230612641983592219616
    keccak([hb[GEN ** 0], hb[GEN ** 1]], [hb[GEN ** 2], hb[GEN ** 3]], out, len=63)
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
