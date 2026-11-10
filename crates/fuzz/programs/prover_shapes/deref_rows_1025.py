# expect: ok
# public_input: GEN ** 5, 0
# Exactly 1025 DEREF rows, every one reading the statement: the DEREF table at a power-of-two edge.
from snark_lib import *

def main():
    hb = HeapBuf(1024)
    p = GEN ** 0
    for i in unroll(0, 1024):
        hb[GEN ** i] = p[1]
    return
