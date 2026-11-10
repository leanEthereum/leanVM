# expect: ok
# public_input: 1, 6
# Every arm calls one function with the same runtime arguments and a varying Const: the compiler fuses the dispatch
# into the callee's entry. A fused callee that returned past the wrong join, or kept the wrong Const, shows here.
from snark_lib import *


def f(a, b, k: Const):
    s = StackBuf(2)
    s[0] = a * GEN ** k
    s[1] = b + k
    return s[0], s[1]


def main():
    hb = HeapBuf(8)
    for i in mul_range(1, GEN ** 8):
        u, v = match(log(i), range(0, 8), lambda k: f(GEN, 7, k))
        assert u == i * GEN
        hb[i] = v
    p = GEN ** 0
    p[1] = hb[GEN ** 6]
    p[GEN] = hb[GEN]
    return
