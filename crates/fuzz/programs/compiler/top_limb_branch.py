# expect: exec-fail JUMP condition is not a K-valued word
# public_input: 7, 9
# Runtime words equal in their two low limbs and different only in the third: assert != sees them as different,
# but a runtime if lowers to a JUMP on a + b, which zkDSL.md requires in K, so the run must fail at the if rather
# than branch on a truncated condition (see top_limb_assert_eq for the assert form, which takes any words).
from snark_lib import *


def main():
    hb = HeapBuf(3)
    hb[1] = f192(5, 6, 0)
    hb[GEN] = f192(5, 6, 7)
    a = hb[1]
    b = hb[GEN]
    assert a != b
    if a == b:
        hb[GEN ** 2] = 8
    else:
        hb[GEN ** 2] = 7
    p = GEN ** 0
    p[1] = hb[GEN ** 2]
    if a + b == f192(0, 0, 7):
        p[GEN] = 9
    else:
        p[GEN] = 10
    return
