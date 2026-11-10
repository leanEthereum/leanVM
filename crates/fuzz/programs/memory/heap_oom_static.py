# expect: exec-fail reaches past
# public_input: 0, 0
# A static HeapBuf of 2^28 cells: the allocator must report OutOfMemory before it touches that much memory.
from snark_lib import *

def main():
    a = HeapBuf(268435456)
    a[1] = 1
    return
