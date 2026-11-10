# expect: ok
# public_input: GEN ** 100000, 0
# witness n: GEN ** 100001
# witness x: GEN ** 100000
# The same missing precheck, with a 2^17-cell heap so x = g^100000 is a real address: the run and the proof must
# agree that log x < log n holds, at a memory size above the minimum the compile-time bounds assume.
from snark_lib import *


def main():
    big = HeapBuf(131072)
    big[GEN ** 131071] = 1
    n = hint_witness("n")
    x = hint_witness("x")
    assert log(x) < log(n)
    p = GEN ** 0
    p[1] = x
    return
