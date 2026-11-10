# expect: prove-fail before anything wrote them
# public_input: 0, 0
# A heap cell nobody writes, used in arithmetic: the value would be the prover's, so prove must refuse the run.
from snark_lib import *

def main():
    hb = HeapBuf(2)
    hb[1] = 1
    x = hb[GEN] * GEN
    y = x + 1
    hb[1] = y + x + x
    return
