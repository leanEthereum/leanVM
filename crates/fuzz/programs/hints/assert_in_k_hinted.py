# expect: exec-fail is not a K-valued word
# witness w: 5 + 18446744073709551616
# `assert_in_k` on a hinted word with a nonzero middle limb: the untaken JUMP reads it as an operand, which must be in
# K, so the run must refuse it; otherwise a non-K limb could pass for a packed half.
from snark_lib import *


def main():
    w = hint_witness("w")
    assert_in_k(w, 3)
    return
