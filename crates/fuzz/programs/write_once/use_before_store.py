# expect: exec-fail write-once conflict
# Uses a heap load in arithmetic before the store that writes the cell: witness generation runs forward, so the use
# sees zero and the later store of a nonzero value must conflict instead of the product being silently wrong. A real
# MUL: `x * GEN` would fold into a pointer and read nothing early.
from snark_lib import *


def main():
    hb = HeapBuf(2)
    x = hb[1]
    y = x * x
    hb[1] = 5
    p = GEN ** 0
    p[1] = y
    return
