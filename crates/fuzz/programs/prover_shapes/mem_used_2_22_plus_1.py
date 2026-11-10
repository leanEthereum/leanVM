# expect: ok
# public_input: 1, 0
# fuzz: slow
# Memory one cell past 2^22: the image pads to 2^23 for a program of a handful of instructions, so memory alone
# dominates the committed witness.
from snark_lib import *

def main():
    hb = HeapBuf(4194299)
    hb[GEN ** 4194298] = 1
    p = GEN ** 0
    p[1] = hb[GEN ** 4194298]
    return
