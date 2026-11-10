# expect: ok
# public_input: GEN ** 11, 0
# Exactly 16 instructions of code (an unroll of 10 MULs plus the fixed six): the padded bytecode size and the halt
# sentinel at its last slot must never collide with a real instruction at the power-of-two edge. Pinned by count.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = GEN
    g = hb[1]
    acc = hb[1]
    for i in unroll(0, 10):
        acc = acc * g
    p = GEN ** 0
    p[1] = acc
    return
