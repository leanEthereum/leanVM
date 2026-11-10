# expect: ok
# public_input: 9, 9
# `addr(sb)` first materialized (fp through a heap bounce) inside a skipped branch, then again after the join: the
# materialized fp cell must not be reused on the path that skipped it.
from snark_lib import *


def f(c):
    sb = StackBuf(2)
    sb[0] = 9
    sb[1] = 10
    if c == 1:
        q = addr(sb)
        assert q[1] == 9
    ptr = addr(sb)
    return ptr[1]


def main():
    a = f(0)
    b = f(1)
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
