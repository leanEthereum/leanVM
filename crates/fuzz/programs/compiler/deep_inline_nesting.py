# expect: ok
# public_input: GEN ** 144, GEN ** 112
# Six levels of @inline, each calling the level below twice with Const arguments k and k + 1 (64 leaf copies):
# k + 1 in a Const argument is integer arithmetic, so an XOR reading (1 + 1 = 0) would change the exponent.
from snark_lib import *

@inline
def l1(x, k: Const):
    y = x * GEN ** k
    return y

@inline
def l2(x, k: Const):
    y = l1(x, k + 1) * l1(x, k)
    return y

@inline
def l3(x, k: Const):
    y = l2(x, k + 1) * l2(x, k)
    return y

@inline
def l4(x, k: Const):
    y = l3(x, k + 1) * l3(x, k)
    return y

@inline
def l5(x, k: Const):
    y = l4(x, k + 1) * l4(x, k)
    return y

@inline
def l6(x, k: Const):
    y = l5(x, k + 1) * l5(x, k)
    return y

def main():
    hb = HeapBuf(1)
    hb[1] = GEN
    x = hb[1]
    p = GEN ** 0
    p[1] = l6(x, 1)
    p[GEN] = l6(x, 0)
    return
