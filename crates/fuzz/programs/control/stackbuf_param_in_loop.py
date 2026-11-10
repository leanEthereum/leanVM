# expect: ok
# public_input: 3, 0
# A StackBuf argument to a callee inside a mul_range body: the run is captured by the loop, copied per iteration, then
# passed whole, where the callee pins every cell. A miscopy at any step conflicts.
from snark_lib import *


def check(s: StackBuf(3), i):
    s[0] = 3
    s[1] = 5
    s[2] = i * s[2] / i
    return s[0]


def main():
    sb = StackBuf(3)
    sb[0] = 3
    sb[1] = 5
    sb[2] = 9
    for i in mul_range(GEN, GEN ** 6):
        r = check(sb, i)
        assert r == 3
    p = GEN ** 0
    p[1] = sb[0]
    return
