# expect: exec-fail write-once conflict
# A heap cell stored twice with different values through an aliasing view: the run must refuse it, since the second
# store is the equality assertion every publish and keccak check is built on.
from snark_lib import *


def main():
    hb = HeapBuf(4)
    hb[GEN ** 2] = 9
    view = hb * GEN
    view[GEN] = 10
    return
