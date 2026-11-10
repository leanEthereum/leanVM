# expect: ok
# public_input: 0, 0
# Exactly 1025 XOR rows (and no KECCAK rows): the XOR table at a power-of-two edge.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = GEN
    g = hb[1]
    acc = hb[1]
    for i in unroll(0, 1025):
        acc = acc + g
    out = HeapBuf(1)
    out[1] = acc
    return
