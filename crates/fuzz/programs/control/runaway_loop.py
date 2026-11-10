# expect: exec-fail loop bound is not a g-power
# witness n: 5
# A runtime mul_range bound that is not a small g-power and was never range-checked: the walk can never reach it, and
# the run must end with a clean fault rather than spin or crash.
from snark_lib import *


def main():
    n = hint_witness("n")
    for i in mul_range(1, n):
        assert_gpow(i)
    return
