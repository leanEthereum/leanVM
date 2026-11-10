# expect: ok
# A constant array holding a field value written in place, `GEN ** 5`, beside an integer: each element must read back
# as itself, the g-power as a field value and usable as an index, never silently as some integer.
from snark_lib import *

S = [3, GEN ** 5]
G5 = GEN ** 5


def main():
    hb = HeapBuf(6)
    hb[1] = S[1]
    assert hb[1] == G5
    hb[GEN] = S[0]
    assert hb[GEN] == 3
    hb[S[1]] = 9
    assert hb[GEN ** 5] == 9
    p = GEN ** 0
    p[1] = hb[1] * hb[GEN]
    return
