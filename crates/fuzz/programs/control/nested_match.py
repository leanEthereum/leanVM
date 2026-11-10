# expect: ok
# public_input: 23, 5
# A match whose arms call functions that themselves match, and a match inside a loop body: each dispatch reads its
# own table in main's frame, so tables that collide or slots read at the wrong offset pick the wrong arm.
from snark_lib import *

INNER = [3, 5, 7, 11]
OUTER = [13, 17, 19, 23]


def inner(y):
    v = match(log(y), range(0, 4), lambda k: INNER[k])
    return v


def outer(x, y, j: Const):
    v = inner(y)
    return v + OUTER[j]


def main():
    x = GEN ** 2
    y = GEN ** 1
    r = match(log(x), range(0, 4), lambda j: outer(x, y, j))
    assert r == 5 + 19
    acc = HeapBuf(4)
    for i in mul_range(1, GEN ** 4):
        v = match(log(i), range(0, 4), lambda k: OUTER[k])
        acc[i] = v
    p = GEN ** 0
    p[1] = acc[GEN ** 3]
    p[GEN] = inner(y)
    return
