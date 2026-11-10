# expect: ok
# public_input: 255231405766226377092371489783609217733, 149727777142906939876210071365441945829
# keccak at len=0: the padding byte lands at byte 0 of the 64-byte operand pair, and every cell wholly past the
# message is a literal zero. The digest is pre-written from an independent Keccak-256, so any misplaced padding conflicts.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    out = StackBuf(2)
    out[0] = 255231405766226377092371489783609217733
    out[1] = 149727777142906939876210071365441945829
    keccak([0, 0], [0, 0], out, len=0)
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
