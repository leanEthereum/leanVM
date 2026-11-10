# expect: ok
# public_input: GEN ** 14, 11
# A chain of @inline helpers four deep, one returning a StackBuf alias, one in expression position, one with a Const
# that folds an `if`: the expansion must keep each level's locals apart.
from snark_lib import *


@inline
def l3(a, k: Const):
    s = StackBuf(2)
    if k % 2 == 0:
        s[0] = a * GEN
    else:
        s[0] = a * GEN ** 2
    s[1] = a
    return s


@inline
def l2(a, k: Const):
    t = l3(a, k)
    return t[0] * GEN


@inline
def l1(a):
    x = l2(a, 0) * l2(a, 1)
    return x


@inline
def l0(a):
    return l1(a) * GEN ** 5


def main():
    r = l0(GEN ** 2)
    v = 3 + l2(1, 0)
    p = GEN ** 0
    p[1] = r
    p[GEN] = v + 3 + 4 + 11
    return
