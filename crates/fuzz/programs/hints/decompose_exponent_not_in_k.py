# expect: exec-fail is not a K-valued word
# witness y: 18446744073709551616
# The exponent decomposition of the tower element y, outside K: the hint must refuse the word, not take its low limb
# (zero) or loop in the discrete log.
from snark_lib import *


def main():
    y = hint_witness("y")
    bits = StackBuf(8)
    hint_decompose_bits_exponent(bits, y, 8)
    return
