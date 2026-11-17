# `if` / `elif` / `else` on field equality (`==` / `!=`): one XOR and one
# conditional JUMP. Bindings made inside a branch are branch-local; branches
# communicate through write-once memory: only one branch executes, so both
# may write the same cell. The loop body's `if` runs in a helper frame (its
# own fp cell). Published: (5, 13 + 17) = (5, 28): `+` is XOR.
# public_input: 5, 28
from snark_lib import *


def main():
    r = HeapBuf(4)
    x = GEN ** 3
    if x == GEN ** 3:
        r[1] = 5
    else:
        r[1] = 7
    if x == GEN:
        r[GEN] = 11
    elif x == GEN ** 3:
        r[GEN] = 13
    else:
        r[GEN] = 15
    for i in mul_range(1, GEN ** 4):
        if i == GEN ** 2:
            r[GEN ** 2] = 17
    p = GEN ** 0
    p[1] = r[1]
    p[GEN] = r[GEN] + r[GEN ** 2]
    return
