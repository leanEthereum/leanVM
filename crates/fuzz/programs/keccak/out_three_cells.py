# expect: compile-error
# A 3-cell out: an instruction writes the first 1, 2 or 13 cells of the state only, so any other width must be
# refused at compile time.
from snark_lib import *


def main():
    out = StackBuf(3)
    keccak([1, 2], [3, 4], out)
    return
