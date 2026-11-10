# expect: exec-fail HeapBuf size is not a g-power in range
# witness n: GEN ** 2147483648
# A runtime HeapBuf size of 2^31 cells: the allocation passes the address space the interpreter supports and must
# fail cleanly, not abort the process.
from snark_lib import *


def main():
    n = hint_witness("n")
    hb = HeapBuf(n)
    hb[1] = 1
    return
