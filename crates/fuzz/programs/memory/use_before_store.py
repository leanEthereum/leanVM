# expect: exec-fail write-once conflict
# public_input: 15, 0
# A load used in a real MUL before the store that gives it a value: witness generation reads zero, and the later
# store must conflict rather than leave the product computed from a value the cell never holds.
from snark_lib import *

def main():
    hb = HeapBuf(2)
    hb[GEN] = 3
    k = hb[GEN]
    x = hb[1]
    y = x * k
    hb[1] = 5
    p = GEN ** 0
    p[1] = y
    return
