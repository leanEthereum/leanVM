# expect: exec-fail not a small g-power
# witness i: 0
# A heap store at runtime index 0: the pointer buf * 0 is zero, which addresses nothing, so the DEREF must fault
# rather than alias some cell.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    i = hint_witness("i")
    hb[i] = 5
    return
