# expect: ok
# public_input: 2 + 4 * GEN, 27
# The two arithmetic regimes side by side: 3 + 1 is the field 2 in a value, the integer 4 in a global, a const(...)
# or a size; 2 ** 64 in a value is the reduced power x^4 + x^3 + x + 1 = 27, const(2 ** 64) the tower element y.
from snark_lib import *

STEP = 3 + 1

def main():
    hb = HeapBuf(6)
    hb[1] = 3 + 1
    hb[GEN] = const(3 + 1)
    hb[GEN ** 2] = STEP
    hb[GEN ** 3] = 2 ** 64
    hb[GEN ** 4] = const(2 ** 64)
    assert hb[1] == 2
    assert hb[GEN] == 4
    assert hb[GEN ** 2] == 4
    assert hb[GEN ** 3] == 27
    assert hb[GEN ** 4] == 18446744073709551616
    sb = StackBuf(STEP)
    sb[STEP - 1] = 7
    if const(3 + 1 == 4):
        escaped = 5
    hb[GEN ** 5] = escaped
    assert hb[GEN ** 5] == 5
    p = GEN ** 0
    p[1] = hb[1] + hb[GEN] * GEN
    p[GEN] = hb[GEN ** 3]
    return
