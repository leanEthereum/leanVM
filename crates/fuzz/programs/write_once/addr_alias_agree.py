# expect: ok
# public_input: 5, GEN ** 7
# Writes a frame cell through a runtime `addr` pointer and reads it back by name, in a callee that materializes its
# own fp: the pointer and the direct cell must be the same cell in a non-main frame too.
from snark_lib import *


def fill(v):
    sb = StackBuf(3)
    ptr = addr(sb)
    j = GEN * GEN
    ptr[j] = v
    sb[0] = GEN ** 7
    return sb[2], ptr[1]


def main():
    a, b = fill(5)
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
