# expect: ok
# public_input: GEN ** 3000, 0
# Non-tail recursion 3000 frames deep, each frame consuming its callee's return: frames must stay disjoint at depth,
# or a deep frame overwrites a live caller's cell.
from snark_lib import *


def down(x, n):
    if x == n:
        return x
    r = down(x * GEN, n)
    assert r == n
    return r


def main():
    v = down(1, GEN ** 3000)
    p = GEN ** 0
    p[1] = v
    return
