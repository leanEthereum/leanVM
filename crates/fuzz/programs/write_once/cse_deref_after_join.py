# expect: ok
# public_input: 41, 41
# The same heap read `hb[i]` inside a branch and after the join: identical pure operations share a cell, except
# across a branch. On the skipping path, reusing the branch's cell would read it unwritten.
from snark_lib import *


def f(hb, i, c):
    r = HeapBuf(1)
    if c == 1:
        r[1] = hb[i]
    v = hb[i]
    return v


def main():
    hb = HeapBuf(4)
    hb[GEN ** 2] = 41
    a = f(hb, GEN ** 2, 0)
    b = f(hb, GEN ** 2, 1)
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
