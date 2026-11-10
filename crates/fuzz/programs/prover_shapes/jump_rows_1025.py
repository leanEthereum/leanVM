# expect: ok
# public_input: 0, 0
# Exactly 1025 JUMP rows, all but the halt untaken assert_in_k jumps: the JUMP table at a power-of-two edge.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = GEN
    g = hb[1]
    for i in unroll(0, 1024):
        assert_in_k(g, g)
    return
