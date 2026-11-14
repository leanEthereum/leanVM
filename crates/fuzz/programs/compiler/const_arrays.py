# expect: ok
# public_input: 9, 5
# Constant arrays read in both regimes: const(S[0] * 3) multiplies the bit pattern (9), S[0] * 3 is a field product
# ((x + 1)^2 = 5). len() drives an unroll whose indices fold into heap offsets; a field element enters through a named constant.
from snark_lib import *

G5 = GEN ** 5
S = [3, 7, G5, 18446744073709551616]

def main():
    hb = HeapBuf(4)
    for i in unroll(0, len(S)):
        hb[GEN ** i] = S[i]
    assert hb[GEN ** 2] == GEN ** 5
    assert hb[GEN ** 3] * hb[1] == 18446744073709551616 * 3
    out = HeapBuf(2)
    out[1] = const(S[0] * 3)
    out[GEN] = S[0] * 3
    p = GEN ** 0
    p[1] = out[1]
    p[GEN] = out[GEN]
    return
