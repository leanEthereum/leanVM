# expect: exec-fail hint_decompose_bits_exponent value is not a g-power
# x = 5 is a g-power with a huge exponent, decomposed at nbits 40: the bounded discrete log walks 2^23 giant steps
# before giving up. The hint's cost must stay bounded by nbits and end in a fault, not a hang.
from snark_lib import *


def main():
    bits = StackBuf(40)
    hint_decompose_bits_exponent(bits, 5, 40)
    return
