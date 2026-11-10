# expect: ok
# public_input: GEN ** 5, GEN ** 45
# A loop with reserved frames whose body allocates a HeapBuf and calls a function that allocates its own: the doc says
# calls and heap allocations stay disjoint from the reserved run, so no buffer may overlap another iteration's frame.
from snark_lib import *


def mk(v):
    b = HeapBuf(2)
    b[1] = v
    b[GEN] = v * GEN
    return b


def main():
    ptrs = HeapBuf(6)
    for i in mul_range(1, GEN ** 6):
        local = HeapBuf(3)
        local[1] = i
        local[GEN] = i + 1
        local[GEN ** 2] = i * i
        b = mk(i)
        assert b[GEN] == i * GEN
        assert local[GEN ** 2] == i * i
        ptrs[i] = local
    last = ptrs[GEN ** 5]
    acc = 1
    for k in unroll(0, 6):
        q = ptrs[GEN ** k]
        acc = acc * q[GEN ** 2] * q[1]
    p = GEN ** 0
    p[1] = last[1]
    p[GEN] = acc
    return
