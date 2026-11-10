# expect: ok
# public_input: GEN ** 4097, GEN ** 4096
# A 4096-copy unroll twice: once as folded pointer offsets (zero instructions), once as 4096 real MULs.
# Both must land on g^4096 times the start.
from snark_lib import *

def main():
    hb = HeapBuf(2)
    hb[1] = GEN
    hb[GEN] = 1
    x = hb[1]
    g = hb[1]
    acc = hb[GEN]
    folded = hb[GEN]
    for i in unroll(0, 4096):
        acc = acc * g
        folded = folded * GEN
    p = GEN ** 0
    p[1] = acc * x
    p[GEN] = folded
    return
