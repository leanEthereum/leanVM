# expect: compile-error heap index 4 out of bounds for `a`
# A compile-time index one past a HeapBuf must be rejected, not wrapped into the next allocation.
from snark_lib import *

def main():
    a = HeapBuf(4)
    b = HeapBuf(4)
    a[GEN ** 4] = 7
    b[1] = 7
    return
