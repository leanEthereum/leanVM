# expect: ok
# public_input: 777, 777
# A pooled constant first SET inside a branch, then used again after the join: on the path that skips the branch the
# lazily-set cell is unwritten, so the compiler must SET it again. Run with the branch taken and skipped.
from snark_lib import *


def f(x):
    r = HeapBuf(2)
    if x == GEN:
        r[1] = 777
    r[GEN] = 777
    return r[GEN]


def main():
    a = f(GEN)
    b = f(GEN ** 2)
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
