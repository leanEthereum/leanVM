# expect: ok
# public_input: 0, 0
# Close to one row in every table, KECCAK included (far below its floor): the smallest nonempty shape of each table.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = GEN
    g = hb[1]
    x = g * g + g
    d = StackBuf(2)
    keccak([0, 0], [0, 0], d)
    assert d[0] != x
    return
