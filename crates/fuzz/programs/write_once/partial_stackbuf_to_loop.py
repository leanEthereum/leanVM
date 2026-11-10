# expect: prove-fail before anything wrote them
# public_input: 2, 0
# Passes a StackBuf with one unwritten cell into a mul_range body that reads it: every captured cell is copied each
# iteration, so the unwritten one becomes prover-chosen and prove must refuse the run.
from snark_lib import *


def main():
    sb = StackBuf(3)
    sb[0] = 1
    sb[1] = 2
    out = HeapBuf(4)
    for i in mul_range(1, GEN ** 3):
        out[i] = sb[2] + i
    p = GEN ** 0
    p[1] = out[GEN]
    return
