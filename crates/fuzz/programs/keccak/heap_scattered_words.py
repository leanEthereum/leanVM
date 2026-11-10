# expect: ok
# public_input: 1, 0
# keccak_cells over scattered heap words named in a list comprehension, against the same words copied into a stack
# run: words read where they lie must hash exactly as a consecutive run, across a block boundary.
from snark_lib import *


def main():
    hb = HeapBuf(30)
    for i in mul_range(1, GEN ** 30):
        hb[i] = i * i
    run = StackBuf(10)
    for k in unroll(0, 10):
        run[k] = hb[GEN ** (3 * k)]
    a = StackBuf(2)
    keccak_cells([hb[GEN ** (3 * k)] for k in unroll(0, 10)], a)
    b = StackBuf(2)
    keccak_cells(run, b)
    c = HeapBuf(2)
    keccak_cells(run[0:10], c[0:2])
    assert a[0] == b[0]
    assert a[1] == b[1]
    assert c[1] == b[0]
    assert c[GEN] == b[1]
    p = GEN ** 0
    p[1] = 1
    return
