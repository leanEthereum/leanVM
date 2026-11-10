# expect: ok
# public_input: GEN ** 1999, GEN ** 3998
# 2000 allocations in a loop, each pointer recorded and the cells re-read in a second loop:
# the bump allocator must keep every buffer disjoint across loop frames.
from snark_lib import *

def main():
    rec = HeapBuf(2000)
    for i in mul_range(1, GEN ** 2000):
        b = HeapBuf(2)
        b[1] = i
        b[GEN] = i * i
        rec[i] = b
    for j in mul_range(1, GEN ** 2000):
        b = rec[j]
        assert b[GEN] == b[1] * b[1]
    last = rec[GEN ** 1999]
    p = GEN ** 0
    p[1] = last[1]
    p[GEN] = last[GEN]
    return
