# expect: ok
# public_input: 147972722503467448341495417196481380704, 8295594661905532710735229566295186221
# keccak at len=1: the padding byte lands at byte 1 of the 64-byte operand pair, and every cell wholly past the
# message is a literal zero. The digest is pre-written from an independent Keccak-256, so any misplaced padding conflicts.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    hb[GEN ** 0] = 11
    out = StackBuf(2)
    out[0] = 147972722503467448341495417196481380704
    out[1] = 8295594661905532710735229566295186221
    keccak([hb[GEN ** 0], 0], [0, 0], out, len=1)
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
