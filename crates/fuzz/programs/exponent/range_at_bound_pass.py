# expect: ok
# public_input: GEN ** 65535, GEN ** 7
# Range checks exactly at their bounds: g^(k-1) < k for k = 1, 2, 8 and the maximum 2^16. An off-by-one in the
# complement g^(k-1) / x would reject the largest element.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    hb[1] = GEN ** 0
    hb[GEN] = GEN ** 1
    hb[GEN ** 2] = GEN ** 7
    hb[GEN ** 3] = GEN ** 65535
    assert log(hb[1]) < 1
    assert log(hb[GEN]) < 2
    assert log(hb[GEN ** 2]) < 8
    assert log(hb[GEN ** 2]) < log(GEN ** 8)
    assert log(hb[GEN ** 3]) < 65536
    p = GEN ** 0
    p[1] = hb[GEN ** 3]
    p[GEN] = hb[GEN ** 2]
    return
