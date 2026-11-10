# expect: ok
# public_input: 149972726020045445386658168898358283277, 155203909643935651413725168260676818039
# keccak with a tail operand at len=128: the message spans a, b and part of tail, and the padding lands
# in the last tail cell. The digest is pre-written from an independent Keccak-256, so a misplaced padding byte or a
# cell dropped from the tail conflicts.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    hb[GEN ** 0] = 71871383284339455167932608602839527435
    hb[GEN ** 1] = 178621423072424560128051388010014802011
    hb[GEN ** 2] = 285376675360240156043455777163709894827
    hb[GEN ** 3] = 50520332810868806498481338092594995451
    hb[GEN ** 4] = 157270372598953911440153373426060718155
    hb[GEN ** 5] = 264025624886769507355557762579755810971
    hb[GEN ** 6] = 30498510333183073683487130568921256171
    hb[GEN ** 7] = 135919342407892866403926064264334630971
    out = StackBuf(2)
    out[0] = 149972726020045445386658168898358283277
    out[1] = 155203909643935651413725168260676818039
    keccak([hb[GEN ** 0], hb[GEN ** 1]], [hb[GEN ** 2], hb[GEN ** 3]], out, tail=[hb[GEN ** 4], hb[GEN ** 5], hb[GEN ** 6], hb[GEN ** 7]], len=128)
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
