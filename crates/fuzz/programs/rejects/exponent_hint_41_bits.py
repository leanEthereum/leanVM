# expect: compile-error writes at most 40 bits
# The exponent search behind hint_decompose_bits_exponent is a bounded discrete log: past 40 bits a hand-written program
# could make its own prover search for hours, so the compiler caps the width.
from snark_lib import *


def main():
    bits = StackBuf(41)
    hint_decompose_bits_exponent(bits, GEN ** 3, 41)
    return
