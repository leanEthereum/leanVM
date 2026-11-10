# expect: exec-fail hint_decompose_bits_exponent value is not a g-power
# witness z: 0
# The exponent decomposition of 0, which has no discrete log: the hint must fault instead of writing some bits.
from snark_lib import *


def main():
    z = hint_witness("z")
    bits = StackBuf(8)
    hint_decompose_bits_exponent(bits, z, 8)
    return
