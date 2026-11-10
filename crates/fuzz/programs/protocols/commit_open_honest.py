# expect: ok
# public_input: 233278316773268983500668275007982421763, 143726631603144034357595415086889223388
# witness open: GEN ** 700, 123456789
# The honest opening of a commitment to g^700.
from snark_lib import *

# Commit-then-open: the statement is H(v, nonce, 0, 0); the opening hints v and the nonce, and the program also proves
# v is a g-power below 2^10.


def main():
    o = StackBuf(2)
    hint_witness(o, "open")
    c = StackBuf(2)
    keccak(o, [0, 0], c)
    assert log(o[0]) < 1024
    p = GEN ** 0
    p[1] = c[0]
    p[GEN] = c[1]
    return
