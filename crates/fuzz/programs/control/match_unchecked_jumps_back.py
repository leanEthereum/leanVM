# expect: exec-fail witness stream `x` exhausted
# witness x: GEN ** 4
# An unchecked scrutinee one past the table: the slot read holds an earlier pc, so the dispatch jumps backwards and
# re-runs the hint, which finds its stream empty. Shows the dispatch is an arbitrary jump without the range check.
from snark_lib import *


def main():
    a = GEN ** 3
    b = GEN ** 9
    c = GEN ** 17
    hb = HeapBuf(4)
    hb[1] = a
    hb[GEN] = b
    hb[GEN ** 2] = c
    x = hint_witness("x")
    r = match(log(x), range(0, 4), lambda k: k * 2 + 1)
    p = GEN ** 0
    p[1] = r
    return
