# expect: compile-error would name two different cells
# `hb[3 + 7]` is the integer 10 as an index but the field element 2 (g^2) as a value: the compiler must refuse to guess
# which cell is meant rather than silently read one of them.
from snark_lib import *


def main():
    hb = HeapBuf(16)
    hb[3 + 7] = 5
    return
