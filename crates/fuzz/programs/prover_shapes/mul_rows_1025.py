# expect: ok
# public_input: GEN ** 1026, 0
# Exactly 1025 MUL rows and no XOR or KECCAK rows: the MUL table at the power-of-two edge, two tables empty.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = GEN
    g = hb[1]
    acc = hb[1]
    for i in unroll(0, 1025):
        acc = acc * g
    p = GEN ** 0
    p[1] = acc
    return
