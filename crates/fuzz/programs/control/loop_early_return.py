# expect: ok
# public_input: GEN ** 3, 0
# A bare `return` in a mul_range body ends the whole loop: iterations past it would hit a range check that fails, so
# a lowering that only skipped the rest of one iteration would be caught.
from snark_lib import *


def main():
    out = HeapBuf(10)
    for i in mul_range(1, GEN ** 10):
        out[i] = i
        if i == GEN ** 3:
            return
        assert log(i) < 3
    p = GEN ** 0
    p[1] = out[GEN ** 3]
    return
