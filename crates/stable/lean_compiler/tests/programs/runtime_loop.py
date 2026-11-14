# A runtime mul_range stop bound: the loop walks ×GEN from the start element
# until it reaches a *runtime* g-power: here a hinted count, range-checked
# first (an unreachable bound would never terminate, so bounding the log is
# the program's duty). Repeated squaring: buf[g^k] holds g^{2^k}, so after
# n = 5 iterations buf[n] = g^32. The second loop's hinted bound equals its
# start: zero iterations, its impossible assert never runs.
# Published: (g^32, g^5).
# public_input: GEN ** 32, GEN ** 5
# witness n: GEN ** 5
# witness m: 1
from snark_lib import *


def main():
    nb = StackBuf(1)
    hint_witness(nb[0:1], "n")
    n = nb[0]
    assert log(n) < 16
    buf = HeapBuf(40)
    buf[1] = GEN
    for i in mul_range(1, n):
        buf[i * GEN] = buf[i] * buf[i]
    mb = StackBuf(1)
    hint_witness(mb[0:1], "m")
    m = mb[0]
    assert log(m) < 16
    for j in mul_range(1, m):
        assert 1 == 0  # empty runtime range: never entered
    p = GEN ** 0
    p[1] = buf[n]
    p[GEN] = n
    return
