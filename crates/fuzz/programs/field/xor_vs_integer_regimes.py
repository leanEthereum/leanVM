# expect: ok
# public_input: 2, 4
# The same text `3 + 1` in two regimes: a global constant is the integer 4, a local binding is the field element 2.
# If the compiler mixed them, the published words or the derived buffer size would come out wrong.
from snark_lib import *

STEP = 3 + 1


def main():
    x = 3 + 1
    assert x == 2
    buf = StackBuf(STEP)
    buf[STEP - 1] = 4
    y = const(3 + 1)
    assert y == STEP
    p = GEN ** 0
    p[1] = x
    p[GEN] = buf[3]
    return
