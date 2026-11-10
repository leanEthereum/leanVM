# expect: exec-fail not a small g-power
# witness n: GEN ** 100
# witness x: GEN ** 100
# A hinted x equal to its runtime bound: log x = k fails log x < k, so the complement is g^(-1) and its DEREF must
# fault.
from snark_lib import *


def main():
    n = hint_witness("n")
    assert log(n) < 65536
    x = hint_witness("x")
    assert log(x) < log(n)
    return
