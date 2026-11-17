# The Fibonacci benchmark (`bins/leanvm`, `cargo leanvm fibonacci --n N`): Fibonacci in the
# exponent over N = 1000·B steps, `buff[g^k]` holding g^F(k). The block count B is read at run time
# from the second public word, g^B, so one compiled program serves every N: block j reads its
# boundary pair at cells g^{2j}, g^{2j+1} (its base `b = x·x` for the loop counter x = g^j), runs
# 1000 Fibonacci MULs in frame cells, and writes the next pair. Published: (g^F(N), g^B).
# Here N = 2000: F(2000) mod 2^64 - 1 = 4133460837788448765.
# public_input: 8035997182686239527, GEN ** 2
from snark_lib import *


def main():
    public = GEN ** 0
    end = public[GEN]
    assert log(end) < 16385
    buff = HeapBuf(end * end * GEN ** 2)
    buff[1] = 1
    buff[GEN] = GEN
    for x in mul_range(1, end):
        b = x * x
        f = StackBuf(1002)
        f[0] = buff[b]
        f[1] = buff[b * GEN]
        for j in unroll(2, 1002):
            f[j] = f[j - 2] * f[j - 1]
        buff[b * GEN ** 2] = f[1000]
        buff[b * GEN ** 3] = f[1001]
    public[1] = buff[end * end]
    return
