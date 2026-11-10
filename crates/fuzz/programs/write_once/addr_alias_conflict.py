# expect: exec-fail write-once conflict
# Writes a frame cell through a runtime `addr` pointer, then stores a different value into the same cell by its
# StackBuf name: the two spellings are one cell, so the direct store must conflict.
from snark_lib import *


def main():
    sb = StackBuf(3)
    ptr = addr(sb)
    j = GEN * GEN
    ptr[j] = 5
    sb[2] = 6
    return
