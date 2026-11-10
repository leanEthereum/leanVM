# expect: ok
# public_input: GEN ** 12, GEN ** 66
# witness n: GEN ** 12
# A hinted loop bound, range-checked, driving a loop that sums exponents with a nested compile-time unroll: the
# runtime bound is threaded as an extra argument, so a lost argument changes the trip count.
from snark_lib import *


def main():
    n = hint_witness("n")
    assert log(n) < 64
    acc = HeapBuf(13)
    acc[1] = 1
    for i in mul_range(1, n):
        v = acc[i] * i
        for k in unroll(0, 1):
            acc[i * GEN] = v
    p = GEN ** 0
    p[1] = n
    p[GEN] = acc[n]
    return
