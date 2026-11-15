# `hint_witness(dest, "name")` pops the next *entry* (a slice of values) of a
# named prover stream into a StackBuf or a StackBuf/HeapBuf slice: zero
# cycles, and completely unconstrained: every hinted value below is pinned
# down by the program itself (a range check, equality asserts, an XOR
# relation). The same symbol may be hinted many times: each `# witness` line
# is one entry, and the two pops of "r" consume its two entries in order.
# Published: (GEN ** 5, 6).
# public_input: GEN ** 5, 6
# witness r: GEN ** 5, 12
# witness r: 9
# witness h: 3, 5, 6
from snark_lib import *


def main():
    sb = StackBuf(2)
    hint_witness(sb, "r")  # first "r" entry: (GEN ** 5, 12)
    assert log(sb[0]) < 8  # constrain the hinted g-power
    assert sb[1] == 12
    hb = HeapBuf(4)
    hint_witness(hb[0:3], "h")  # heap slice: the (3, 5, 6) entry
    assert hb[1] + hb[GEN] == hb[GEN ** 2]  # constrain: 3 + 5 = 6 (XOR)
    hint_witness(hb[3:4], "r")  # second "r" entry: (9)
    assert hb[GEN ** 3] == 9
    p = GEN ** 0
    p[1] = sb[0]
    p[GEN] = hb[GEN ** 2]
    return
