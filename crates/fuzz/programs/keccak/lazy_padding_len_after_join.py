# expect: ok
# public_input: 294158050071697034368632837271588659664, 202403740803834135684315465766773895334
# A len=31 keccak (padding inside a program cell, one XOR) in a branch, then the same hash after the join, on the
# skipping path: the padded cell computed inside the branch must not be reused after it.
from snark_lib import *


def h(c):
    a = 71871383284339455167932608602839527435
    b = 504871637245833158941241932448628827
    if c == 1:
        t = StackBuf(2)
        keccak([a, b], [0, 0], t, len=31)
    out = StackBuf(2)
    keccak([a, b], [0, 0], out, len=31)
    return out[0], out[1]


def main():
    x, y = h(0)
    u, v = h(1)
    assert x == u
    assert y == v
    p = GEN ** 0
    p[1] = x
    p[GEN] = y
    return
