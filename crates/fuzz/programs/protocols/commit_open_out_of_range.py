# expect: exec-fail failed range check
# public_input: 105631395110240216611528231564740482484, 158019414624691348484789030219118331871
# witness open: GEN ** 2000, 123456789
# An honest opening of a commitment to g^2000: the hash matches, the range property must not.
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
