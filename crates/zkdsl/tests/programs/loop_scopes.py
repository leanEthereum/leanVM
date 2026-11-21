# Pins what a `mul_range` body binds and what it captures:
# - a name the body binds before it reads it is the body's own, though an
#   `unroll`ed `if` does the binding and the enclosing scope has that name
#   too (`acc`);
# - a binding that never runs, in the other arm of a compile-time `if` or in
#   an `unroll` over nothing, does not hide the enclosing value the body reads
#   (`w`);
# - an `unroll` counter is bound in its body only: after it, the name is the
#   enclosing one again (`k`).
# And a constant that is a g-power indexes its cell: `(GEN ** 2) ** 3` is
# cell 6.
# Published: (g^4 + 7, g^5 + 7 + 9) = (23, 46).
# public_input: 23, 46
from snark_lib import *


def main():
    out = HeapBuf(8)
    acc = 5
    w = GEN ** 3
    k = 7
    for i in mul_range(1, GEN ** 2):
        for j in unroll(0, 2):
            if j == 0:
                acc = i
            else:
                acc = acc * GEN
        if const(1 == 2):
            w = GEN
        for j in unroll(0, 0):
            w = GEN
        for k in unroll(0, 1):
            out[i * GEN ** 4] = k
        out[i] = acc * w + k
    out[(GEN ** 2) ** 3] = 9
    p = GEN ** 0
    p[1] = out[1]
    p[GEN] = out[GEN] + out[GEN ** 6]
    return
