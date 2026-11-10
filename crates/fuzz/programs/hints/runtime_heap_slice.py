# expect: ok
# public_input: 22, 33
# witness pair: 11, 22
# witness pair: 33, 44
# Hints into runtime-start heap slices `buf[i:i + 2]` inside a loop: the pointer is folded per iteration, so each
# entry must land at its own pair of cells and never overlap the next.
from snark_lib import *


def main():
    buf = HeapBuf(4)
    for i in mul_range(1, GEN ** 2):
        j = i * i
        hint_witness(buf[j:j + 2], "pair")
    assert buf[1] + buf[GEN] == 11 + 22
    assert buf[GEN ** 2] == 33
    p = GEN ** 0
    p[1] = buf[GEN]
    p[GEN] = buf[GEN ** 2]
    return
