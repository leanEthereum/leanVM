# expect: ok
# public_input: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8, 0
# witness pairs: 1, 2
# witness pairs: 3, 4
# witness pairs: 5, 6
# witness pairs: 7, 8
# Runtime-start heap slices as hint destinations, one stream entry per loop iteration, then summed.
from snark_lib import *

def main():
    buf = HeapBuf(8)
    for i in mul_range(1, GEN ** 4):
        b = i * i
        hint_witness(buf[b:b + 2], "pairs")
    s = HeapBuf(9)
    s[1] = 0
    for j in mul_range(1, GEN ** 8):
        s[j * GEN] = s[j] + buf[j]
    p = GEN ** 0
    p[1] = s[GEN ** 8]
    p[GEN] = 0
    return
