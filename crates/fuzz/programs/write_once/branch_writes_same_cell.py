# expect: ok
# Both arms of a runtime branch write the same heap cell with different values; only one runs, so the join must read
# the taken arm's value with no conflict, for either outcome of the test.
# public_input: 13, 21
from snark_lib import *


def pick(x):
    r = HeapBuf(1)
    if x == GEN ** 3:
        r[1] = 13
    else:
        r[1] = 21
    return r[1]


def main():
    a = pick(GEN ** 3)
    b = pick(GEN ** 4)
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
