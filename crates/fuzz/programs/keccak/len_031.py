# expect: ok
# public_input: 294158050071697034368632837271588659664, 202403740803834135684315465766773895334
# keccak at len=31: the padding byte lands at byte 31 of the 64-byte operand pair, and every cell wholly past the
# message is a literal zero. The digest is pre-written from an independent Keccak-256, so any misplaced padding conflicts.
from snark_lib import *


def main():
    hb = HeapBuf(8)
    hb[GEN ** 0] = 71871383284339455167932608602839527435
    hb[GEN ** 1] = 504871637245833158941241932448628827
    out = StackBuf(2)
    out[0] = 294158050071697034368632837271588659664
    out[1] = 202403740803834135684315465766773895334
    keccak([hb[GEN ** 0], hb[GEN ** 1]], [0, 0], out, len=31)
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
