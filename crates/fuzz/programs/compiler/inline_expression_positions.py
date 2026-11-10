# expect: ok
# public_input: GEN ** 9, GEN ** 6
# @inline calls in expression position: inside arithmetic, as a store RHS onto an already-written cell (an assert),
# and as a single-target match arm.
from snark_lib import *

@inline
def sq(x):
    y = x * x
    return y

def main():
    hb = HeapBuf(2)
    hb[1] = GEN ** 3
    x = hb[1]
    a = sq(x) * x
    hb[GEN] = GEN ** 6
    hb[GEN] = sq(x)
    s = GEN ** 2
    m = match(log(s), range(0, 3), lambda k: sq(x * GEN ** k))
    assert m == GEN ** 10
    p = GEN ** 0
    p[1] = a
    p[GEN] = hb[GEN]
    return
