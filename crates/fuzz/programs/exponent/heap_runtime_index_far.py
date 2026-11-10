# expect: exec-fail not a small g-power
# witness i: GEN ** 1000000
# A runtime heap index a million cells past a four-cell buffer: unchecked by the compiler, so the interpreter must refuse
# the pointer as outside the memory instead of growing it silently or crashing.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    i = hint_witness("i")
    hb[i] = 7
    return
