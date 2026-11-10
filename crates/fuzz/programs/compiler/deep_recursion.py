# expect: ok
# public_input: GEN ** 3001, 0
# 3000 nested frames counted down by a runtime division, the base case returning from inside an if.
from snark_lib import *

def depth(x, n):
    if n == 1:
        return x
    r = depth(x * GEN, n / GEN)
    return r

def main():
    hb = HeapBuf(1)
    hb[1] = GEN ** 3000
    p = GEN ** 0
    p[1] = depth(GEN, hb[1])
    p[GEN] = 0
    return
