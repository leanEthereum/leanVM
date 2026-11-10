# expect: ok
# Loads a heap cell before the store that gives it its value (legal per the doc), then uses the load after the store:
# the early DEREF must link to the later write, not freeze a zero.
# public_input: 7, GEN ** 3
from snark_lib import *


def main():
    hb = HeapBuf(4)
    x = hb[GEN ** 2]
    i = GEN ** 3
    y = hb[i]
    hb[GEN ** 2] = 7
    hb[GEN ** 3] = GEN ** 3
    p = GEN ** 0
    p[1] = x
    p[GEN] = y
    return
