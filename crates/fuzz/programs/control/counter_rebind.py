# expect: ok
# public_input: GEN ** 8, 2
# Rebinding the loop counter moves the walk: stepping by two from g^0 to g^10 visits even exponents only, so a walk
# that ignored the rebinding would store into the odd cells, which already hold a different value.
from snark_lib import *


def main():
    out = HeapBuf(10)
    out[GEN] = 1
    out[GEN ** 3] = 1
    out[GEN ** 5] = 1
    out[GEN ** 7] = 1
    out[GEN ** 9] = 1
    for i in mul_range(1, GEN ** 10):
        out[i] = 2
        i = i * GEN
    p = GEN ** 0
    p[1] = GEN ** 8
    p[GEN] = out[GEN ** 8]
    return
