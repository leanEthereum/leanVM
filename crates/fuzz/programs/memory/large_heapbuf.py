# expect: ok
# public_input: 3, 4
# A HeapBuf of 2^20 cells written only at its two ends: the untouched middle pads the memory, which must still prove.
from snark_lib import *

def main():
    a = HeapBuf(1048576)
    a[1] = 3
    a[GEN ** 1048575] = 4
    p = GEN ** 0
    p[1] = a[1]
    p[GEN] = a[GEN ** 1048575]
    return
