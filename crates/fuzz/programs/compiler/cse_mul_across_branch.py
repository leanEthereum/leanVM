# expect: ok
# public_input: GEN ** 8, 1
# The same runtime product in an untaken arm (emitted first) and after the join: sharing it across the join would
# read a cell only the untaken arm writes, which is prover-chosen.
from snark_lib import *

def main():
    hb = HeapBuf(3)
    hb[1] = GEN ** 3
    hb[GEN] = GEN ** 5
    a = hb[1]
    b = hb[GEN]
    if a == b:
        t = a * b
        hb[GEN ** 2] = t
    else:
        hb[GEN ** 2] = 1
    u = a * b
    p = GEN ** 0
    p[1] = u
    p[GEN] = hb[GEN ** 2]
    return
