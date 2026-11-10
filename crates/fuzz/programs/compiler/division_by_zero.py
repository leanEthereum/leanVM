# expect: exec-fail cannot back-solve
# public_input: 0, 0
# 5 / 0 has no solution: the back-solve must fault rather than write some quotient.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = 0
    z = hb[1]
    q = 5 / z
    p = GEN ** 0
    p[GEN] = q
    return
