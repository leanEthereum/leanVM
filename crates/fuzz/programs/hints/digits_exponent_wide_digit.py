# expect: compile-error digit_bits
# A 128-bit digit width: the hint's digit mask is 2^digit_bits - 1, which overflows a u128 shift. The compiler must
# refuse the width before the interpreter ever shifts by it.
from snark_lib import *


def main():
    d = StackBuf(1)
    hint_decompose_digits_exponent(d, GEN ** 5, 8, 1, 128, 0)
    return
