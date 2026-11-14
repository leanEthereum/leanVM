# expect: exec-fail not a g-power below 2^28
# witness i: GEN ** 536870912
# A runtime heap index past every addressable cell (2^28): unchecked by the compiler, so the interpreter must
# refuse the pointer instead of growing the memory or crashing.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    i = hint_witness("i")
    hb[i] = 7
    return
