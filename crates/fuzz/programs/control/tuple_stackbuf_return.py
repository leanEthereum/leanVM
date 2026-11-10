# expect: ok
# public_input: 11, 31
# A tuple return mixing two StackBufs of different sizes with scalars between them: the return slots are copied by
# width, so a size off by one shifts every later value into the wrong binding.
from snark_lib import *


def mix(a):
    s = StackBuf(2)
    s[0] = a
    s[1] = a * GEN
    t = StackBuf(3)
    t[0] = 7
    t[1] = 11
    t[2] = 13
    return s, a + 1, t, 31


def main():
    s, u, t, w = mix(GEN ** 4)
    assert s[0] == GEN ** 4
    assert s[1] == GEN ** 5
    assert u == GEN ** 4 + 1
    assert t[0] == 7
    assert t[2] == 13
    p = GEN ** 0
    p[1] = t[1]
    p[GEN] = w
    return
