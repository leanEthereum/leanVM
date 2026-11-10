# expect: exec-fail write-once conflict
# x = g^100 decomposed at nbits 3: 100 does not fit, and the hint must not pretend it does. Here the dlog finds 100
# and writes its low three bits, so the program's rebuild (g^4) disagrees with x and the pin conflicts.
from snark_lib import *


def main():
    c = StackBuf(3)
    x = GEN ** 100
    hint_decompose_bits_exponent(c, x, 3)
    acc = (1 + c[0] * (GEN + 1)) * (1 + c[1] * (GEN ** 2 + 1)) * (1 + c[2] * (GEN ** 4 + 1))
    assert acc == x
    return
