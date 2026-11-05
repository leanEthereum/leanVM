# `match(log(x), range(a, b), lambda j: …)`: x = GEN ** j runs arm j, both the
# match in main and the one in the loop body, a function of its own, through a
# jump table in main's frame. Arms must cover
# consecutive integers from 0, and a hinted scrutinee must be range-checked
# first. Main writes a table where the paths to its match meet: `second`'s in
# both a runtime loop and a branch, `fourth`'s in the branch taken, `third`'s in
# the branch not taken, where it never runs and is never written.
# Published: (21, 5 + 7 + 9 + 5 + 7 + 9 + 200) = (21, 200): `+` is XOR.
# public_input: 21, 200
# witness n: GEN ** 2
from snark_lib import *

FIRST = [11, 17, 21, 27, 31, 37]
SECOND = [5, 7, 9]
FOURTH = [100, 200]


def second(j):
    v = match(log(j), range(0, 3), lambda k: SECOND[k])
    return v


def third(j):
    v = match(log(j), range(0, 2), lambda k: 300 + k)
    return v


def fourth(j):
    v = match(log(j), range(0, 2), lambda k: FOURTH[k])
    return v


def main():
    r = HeapBuf(4)
    x = GEN ** 2
    v = match(log(x), range(0, 6), lambda j: FIRST[j])
    r[1] = v
    for i in mul_range(1, GEN ** 3):
        w = match(log(i), range(0, 3), lambda j: SECOND[j])
        r[i * GEN] = w
    n = hint_witness("n")
    assert log(n) < 3
    s = HeapBuf(3)
    for i in mul_range(1, n):
        s[i] = second(i)
    if n == GEN ** 2:
        s[GEN ** 2] = second(GEN ** 2) + fourth(GEN)
    else:
        s[GEN ** 2] = third(1)
    p = GEN ** 0
    p[1] = r[1]
    p[GEN] = r[GEN] + r[GEN ** 2] + r[GEN ** 3] + s[1] + s[GEN] + s[GEN ** 2]
    return
