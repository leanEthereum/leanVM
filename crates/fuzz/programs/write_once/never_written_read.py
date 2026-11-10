# expect: prove-fail before anything wrote them
# public_input: 5, 0
# Reads a heap cell nobody ever writes and publishes a value computed from it: the run sees zero, but the prover would
# be free to choose it, so prove must refuse the unconstrained read.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    x = hb[GEN ** 3]
    y = x + 5
    p = GEN ** 0
    p[1] = y
    return
