# expect: ok
# public_input: 9, 0
# Two HeapBufs reached from one another by pointer arithmetic (the runtime index b / a): a store through a lands in b,
# so the cross-buffer read sees it. Buffers are a region convention, not isolation.
from snark_lib import *

def main():
    a = HeapBuf(4)
    b = HeapBuf(4)
    d = b / a
    a[d] = 9
    p = GEN ** 0
    p[1] = b[1]
    return
