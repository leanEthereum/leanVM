# expect: ok
# public_input: 10, 0
# A load scaled by GEN before the store that gives it a value: x * GEN is a virtual shifted pointer, materialized only
# at its use after the store, so the run is legal and must publish the stored value's product, never zero.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    x = hb[1]
    y = x * GEN
    hb[1] = 5
    p = GEN ** 0
    p[1] = y
    return
