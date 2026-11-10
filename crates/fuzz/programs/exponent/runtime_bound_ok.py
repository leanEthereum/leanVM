# expect: ok
# public_input: GEN ** 99, GEN ** 100
# witness n: GEN ** 100
# witness x: GEN ** 99
# A hinted runtime bound, itself range-checked to 2^16 first, then a hinted x one below it: the runtime gadget builds
# g^(k-1) = n / g, and must accept the largest element.
from snark_lib import *


def main():
    n = hint_witness("n")
    assert log(n) < 65536
    x = hint_witness("x")
    assert log(x) < log(n)
    p = GEN ** 0
    p[1] = x
    p[GEN] = n
    return
