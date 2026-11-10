# expect: ok
# public_input: GEN ** 4, GEN ** 2 + 1
# A tuple return mixing a StackBuf run, a HeapBuf pointer and a scalar: each part must land in its own binding.
from snark_lib import *

def mk(v):
    s = StackBuf(2)
    s[0] = v
    s[1] = v * v
    h = HeapBuf(1)
    h[1] = v + 1
    return s, h, v * GEN

def main():
    hb = HeapBuf(1)
    hb[1] = GEN ** 2
    s, h, t = mk(hb[1])
    assert t == GEN ** 3
    p = GEN ** 0
    p[1] = s[1]
    p[GEN] = h[1]
    return
