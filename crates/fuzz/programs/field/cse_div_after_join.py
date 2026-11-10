# expect: ok
# public_input: GEN ** 4, GEN ** 4
# The same quotient `a / b` in a skipped branch and after the join, and the same product `a * b`: the back-solved
# quotient cell must be recomputed on the path that skipped the branch, not shared with it.
from snark_lib import *


def f(a, b, c):
    r = HeapBuf(2)
    if c == 1:
        r[1] = a / b
        r[GEN] = a * b
    q = a / b
    s = a * b
    assert s == a * b
    return q


def main():
    u = f(GEN ** 7, GEN ** 3, 0)
    v = f(GEN ** 7, GEN ** 3, 1)
    p = GEN ** 0
    p[1] = u
    p[GEN] = v
    return
