# expect: exec-fail write-once conflict
# A value with bits above nbits (11 = 0b1011 at nbits 2): the hint writes only the low bits, so a program that checks
# the recomposition against the value must fail. A hint that silently widened would hide the truncation.
from snark_lib import *


def main():
    bits = StackBuf(2)
    v = 11
    hint_decompose_bits(bits, v, 2)
    acc = bits[0] + bits[1] * GEN
    assert acc == v
    return
