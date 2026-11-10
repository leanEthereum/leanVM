# expect: compile-error at most 128 bits
# hint_log2_ceil over a 130-bit buffer with bit 129 set: the interpreter accumulates the bits in a u128, so a bit past
# 127 overflows the shift. The compiler must refuse nbits > 128 before the interpreter shifts.
from snark_lib import *


def main():
    bits = StackBuf(130)
    for i in unroll(0, 129):
        bits[i] = 0
    bits[129] = 1
    g = hint_log2_ceil(bits, 130, 0)
    return
