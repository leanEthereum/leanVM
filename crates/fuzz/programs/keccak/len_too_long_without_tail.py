# expect: compile-error
# len=65 with no tail: the operands hold only 64 bytes, so the compiler must refuse rather than read past b.
from snark_lib import *


def main():
    out = StackBuf(2)
    keccak([1, 2], [3, 4], out, len=65)
    return
