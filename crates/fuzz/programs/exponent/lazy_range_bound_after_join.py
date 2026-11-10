# expect: ok
# public_input: GEN ** 7, GEN ** 6
# A range check whose bound cell g^(k-1) is first SET inside a skipped branch, then the same bound used after the
# join: if the compiler reused the branch's cell, the MUL would back-solve against an unwritten bound.
from snark_lib import *


def f(x, c):
    if c == 1:
        assert log(x) < 8
    assert log(x) < 8
    return x


def main():
    a = f(GEN ** 7, 0)
    b = f(GEN ** 6, 1)
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
