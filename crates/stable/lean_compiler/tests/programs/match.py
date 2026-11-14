# `match(log(x), range(a, b), lambda j: …)`: x = GEN ** j runs arm j, both the
# match in main and the one in the loop body, a function of its own, through a
# jump table in main's frame. Arms must cover
# consecutive integers from 0, and a hinted scrutinee must be range-checked
# first. Published: (21, 5 + 7 + 9) = (21, 11): `+` is XOR.
# public_input: 21, 11
from snark_lib import *

FIRST = [11, 17, 21, 27, 31, 37]
SECOND = [5, 7, 9]


def main():
    r = HeapBuf(4)
    x = GEN ** 2
    v = match(log(x), range(0, 6), lambda j: FIRST[j])
    r[1] = v
    for i in mul_range(1, GEN ** 3):
        w = match(log(i), range(0, 3), lambda j: SECOND[j])
        r[i * GEN] = w
    p = GEN ** 0
    p[1] = r[1]
    p[GEN] = r[GEN] + r[GEN ** 2] + r[GEN ** 3]
    return
