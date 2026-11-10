# expect: exec-fail cannot back-solve
# public_input: 0, 0
# 0 / 0 is satisfied by every quotient, so the constraint alone would let the prover choose it: execution refuses.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = 0
    z = hb[1]
    q = z / z
    p = GEN ** 0
    p[1] = q
    return
