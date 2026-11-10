# expect: ok
# public_input: GEN ** 6, GEN ** 9
# Loops that give up reserved frames: one ends early with a bare return (which ends the loop, not main), one rebinds
# its counter to skip ahead. Both must stop and step exactly where the source says.
from snark_lib import *


def main():
    hits = HeapBuf(20)
    for i in mul_range(1, GEN ** 20):
        hits[i] = i
        if i == GEN ** 6:
            return
    last = HeapBuf(1)
    for j in mul_range(1, GEN ** 10):
        if j == GEN ** 2:
            j = GEN ** 8
        if j == GEN ** 9:
            last[1] = j
    p = GEN ** 0
    p[1] = hits[GEN ** 6]
    p[GEN] = last[1]
    return
