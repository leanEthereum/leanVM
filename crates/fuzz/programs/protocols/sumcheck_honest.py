# expect: ok
# public_input: 10, 0
# witness a1: 6
# witness a2: 145311781878722329481337130605930260189
# The honest transcript for the true sum 10.
from snark_lib import *

# A two-round sumcheck verifier over the fixed table [3, 5, 7, 11]: statement word 0 is the claimed sum, the prover
# hints h(0) of each round, challenges come from Keccak over the packed messages (each word split by a hinted top
# limb that KECCAK's canonical input pins), and the final claim is checked against the table's own evaluation.


@inline
def pack(x):
    limbs = StackBuf(3)
    hint_f192_limbs(limbs, x)
    assert_in_k(limbs[2], limbs[2])
    lo = x + f192(0, 0, 1) * limbs[2]
    return lo, limbs[2]


def main():
    p = GEN ** 0
    c = p[1]
    a1 = hint_witness("a1")
    a1_lo, a1_hi = pack(a1)
    c_lo, c_hi = pack(c)
    d1 = StackBuf(2)
    keccak([a1_lo, a1_hi], [c_lo, c_hi], d1)
    r1 = d1[0]
    c1 = a1 + r1 * c
    a2 = hint_witness("a2")
    a2_lo, a2_hi = pack(a2)
    d2 = StackBuf(2)
    keccak([a2_lo, a2_hi], [d1[0], d1[1]], d2)
    r2 = d2[0]
    c2 = a2 + r2 * c1
    s1 = 1 + r1
    s2 = 1 + r2
    g = s1 * s2 * 3 + s1 * r2 * 5 + r1 * s2 * 7 + r1 * r2 * 11
    assert g == c2
    return
