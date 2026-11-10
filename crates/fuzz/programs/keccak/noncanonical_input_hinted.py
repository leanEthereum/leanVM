# expect: exec-fail not a canonical 128-bit embedding
# witness w: 7 + 18446744073709551616 * 18446744073709551616
# A hinted keccak input in the tail run whose top limb is y^2's: the prover chose it, so the canonicity check is all
# that stops a digest of a non-canonical word.
from snark_lib import *


def main():
    t = StackBuf(4)
    hint_witness(t[0:1], "w")
    t[1] = 0
    t[2] = 0
    t[3] = 0
    out = StackBuf(2)
    keccak([1, 2], [3, 4], out, tail=t)
    return
