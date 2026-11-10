# expect: ok
# public_input: GEN ** 6, GEN ** 64
# The statement drives a runtime loop count: range-checked, the loop squares GEN six times and publishes g^(2^6).
from snark_lib import *

def main():
    p = GEN ** 0
    n = p[1]
    assert log(n) < 16
    buf = HeapBuf(17)
    buf[1] = GEN
    for i in mul_range(1, n):
        buf[i * GEN] = buf[i] * buf[i]
    p[GEN] = buf[n]
    return
