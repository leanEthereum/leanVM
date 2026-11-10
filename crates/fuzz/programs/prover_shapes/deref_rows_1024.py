# expect: ok
# public_input: GEN ** 5, 0
# Exactly 1024 DEREF rows, every one reading the statement: the DEREF table at a power-of-two edge.
from snark_lib import *

def main():
    hb = HeapBuf(1023)
    p = GEN ** 0
    for i in unroll(0, 1023):
        hb[GEN ** i] = p[1]
    return
