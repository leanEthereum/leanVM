# expect: ok
# public_input: 76870798587041994854595358325668108629, 156543651484862875866541738639399140452
# A keccak inside a skipped branch sets the five-cell padding run lazily; the keccak after the join needs that run
# too. The doc says it reverts at the join, so the second hash must set it again or read prover-chosen padding.
from snark_lib import *


def h(c):
    m = [242716439218147592190247776532461068291, 178663287798046340062194692478498369747, 114610156739272160164435410271743099043, 50562197615718748928369898115721695347]
    if c == 1:
        t = StackBuf(2)
        keccak(m[0:2], m[2:4], t)
    out = StackBuf(2)
    keccak(m[0:2], m[2:4], out)
    assert out[0] == 76870798587041994854595358325668108629
    return out[0], out[1]


def main():
    a, b = h(0)
    c, d = h(1)
    assert a == c
    p = GEN ** 0
    p[1] = a
    p[GEN] = d
    return
