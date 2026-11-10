# expect: ok
# public_input: 12345, 1
# witness x: GEN ** 6
# A hinted scrutinee past the four arms, never range-checked (the program bug the doc warns of): the dispatch reads a
# slot past the table and jumps to whatever pc it holds, skipping every arm, so the result cell is never written and
# the public input alone fixes it. The prover publishes 12345, which no arm (1, 3, 5, 7) produces.
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
    p[GEN] = 1
    return
