# expect: ok
# public_input: GEN ** 10, GEN ** 4
# Back-to-back matches expanded by an unroll, every arm @inline and writing a StackBuf element that is the next
# match's scrutinee: the compiler chains them, each arm ending in the next dispatch. A chain that dropped, repeated or
# misrouted a step changes the exponent sum.
from snark_lib import *


@inline
def step(k: Const):
    return GEN ** (k + 1)


def main():
    sb = StackBuf(4)
    sb[0] = GEN ** 1
    for t in unroll(0, 3):
        sb[t + 1] = match(log(sb[t]), range(0, 6), lambda k: step(k))
    acc = sb[0] * sb[1] * sb[2] * sb[3]
    p = GEN ** 0
    p[1] = acc
    p[GEN] = sb[3]
    return
