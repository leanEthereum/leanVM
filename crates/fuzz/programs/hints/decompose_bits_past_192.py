# expect: compile-error
# nbits 193 asks for a bit past the 192-bit word: it must be refused while compiling, not reach the interpreter,
# whose decomposition asserts nbits <= 192 and would panic.
from snark_lib import *


def main():
    bits = StackBuf(193)
    hint_decompose_bits(bits, 5, 193)
    return
