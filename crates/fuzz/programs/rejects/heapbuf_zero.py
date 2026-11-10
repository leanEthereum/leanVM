# expect: compile-error heap index 0 out of bounds for `a` (HeapBuf size 0)
# A zero-cell HeapBuf: its pointer would alias the next allocation.
from snark_lib import *

def main():
    a = HeapBuf(0)
    b = HeapBuf(1)
    b[1] = 3
    a[1] = 4
    return
