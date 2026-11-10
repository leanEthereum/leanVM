# expect: ok
# public_input: GEN ** 7, 30
# A callee returns addr() of its own frame run, and the caller reads and re-asserts those cells after the return:
# frames are never reused, so the pointer must stay valid and the values fixed.
from snark_lib import *

def make():
    s = StackBuf(3)
    s[0] = GEN ** 7
    s[1] = 10
    s[2] = 20
    return addr(s)

def main():
    q = make()
    r = make()
    assert q != r
    p = GEN ** 0
    p[1] = q[1]
    p[GEN] = q[GEN] + q[GEN ** 2]
    q[GEN] = 10
    return
