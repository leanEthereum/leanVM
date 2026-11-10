# expect: ok
# public_input: GEN ** 7, GEN ** 3
# Each loop iteration stores a pointer to its own frame run; after the loop the pointers are walked again:
# reserved loop frames must keep every earlier iteration's cells alive and distinct.
from snark_lib import *

def main():
    ptrs = HeapBuf(8)
    for i in mul_range(1, GEN ** 8):
        s = StackBuf(1)
        s[0] = i
        ptrs[i] = addr(s)
    for j in mul_range(1, GEN ** 8):
        q = ptrs[j]
        assert q[1] == j
    p = GEN ** 0
    last = ptrs[GEN ** 7]
    p[1] = last[1]
    third = ptrs[GEN ** 3]
    p[GEN] = third[1]
    return
