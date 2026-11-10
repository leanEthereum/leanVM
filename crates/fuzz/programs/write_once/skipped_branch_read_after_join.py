# expect: prove-fail before anything wrote them
# Writes a cell only in the arm that is skipped, then reads it after the join and publishes it: the cell is
# prover-chosen, so the prover must refuse the run rather than prove a statement about an arbitrary value.
from snark_lib import *


def main():
    r = HeapBuf(2)
    x = GEN ** 2
    if x == GEN ** 5:
        r[GEN] = 99
    v = r[GEN]
    w = v * GEN
    p = GEN ** 0
    p[GEN] = w
    return
