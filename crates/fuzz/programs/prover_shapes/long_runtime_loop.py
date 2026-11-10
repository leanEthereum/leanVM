# expect: ok
# public_input: GEN ** 16384, GEN ** 16384
# witness n: GEN ** 16384
# A runtime loop of 2^14 iterations from a hinted, range-checked count: thousands of reserved frames, every table
# but KECCAK past 2^14 rows, and memory past the 2^16 floor.
from snark_lib import *

def main():
    n = hint_witness("n")
    assert log(n) < 65536
    buf = HeapBuf(16385)
    buf[1] = 1
    for i in mul_range(1, n):
        if i == GEN ** 7:
            buf[i * GEN] = buf[i] * GEN
        else:
            buf[i * GEN] = buf[i] * GEN
    p = GEN ** 0
    p[1] = buf[n]
    p[GEN] = n
    return
