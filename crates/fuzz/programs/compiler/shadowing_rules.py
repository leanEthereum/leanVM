# expect: ok
# public_input: GEN ** 3, 9
# A Const parameter rebound at the body's own level shadows its literal from there on, and an unroll counter rebound
# at its own level likewise: uses before the rebinding keep the literal.
from snark_lib import *

def f(x, k: Const):
    s = StackBuf(4)
    s[k] = x
    a = s[3]
    k = 9
    return a, k

def main():
    hb = HeapBuf(1)
    hb[1] = GEN ** 3
    a, k = f(hb[1], 3)
    acc = GEN
    for i in unroll(0, 3):
        i = i + 1
        acc = acc * GEN ** i
    assert acc == GEN ** 7
    p = GEN ** 0
    p[1] = a
    p[GEN] = k
    return
