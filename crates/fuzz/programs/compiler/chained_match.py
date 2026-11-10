# expect: ok
# public_input: GEN ** 11, 0
# witness d: GEN ** 2, 1, GEN ** 3, GEN
# Back-to-back matches of @inline arms that an unroll expands, which the compiler chains (each arm ending in the next
# dispatch): every digit must still select its own arm, in order.
from snark_lib import *

@inline
def step(acc, k: Const):
    y = acc * GEN ** (k + 1)
    return y

def main():
    ds = StackBuf(4)
    hint_witness(ds, "d")
    for r in unroll(0, 4):
        assert log(ds[r]) < 4
    acc = GEN
    for r in unroll(0, 4):
        acc = match(log(ds[r]), range(0, 4), lambda k: step(acc, k))
    p = GEN ** 0
    p[1] = acc
    p[GEN] = 0
    return
