# expect: ok
# public_input: GEN ** 7, GEN ** 3
# hint_log2_ceil on bit buffers holding 0, 1, 2, 3, 64 and 65, with a floor of 0 and of 3: log2_ceil is 0, 0, 1, 2, 6
# and 7, the floor wins below it. Each result is pinned, so an off-by-one at a power of two conflicts.
from snark_lib import *


@inline
def l2(v, n: Const, floor: Const):
    bits = StackBuf(8)
    hint_decompose_bits(bits, v, 8)
    g = hint_log2_ceil(bits, 8, floor)
    return g


def main():
    assert l2(0, 8, 0) == 1
    assert l2(1, 8, 0) == 1
    assert l2(2, 8, 0) == GEN
    assert l2(3, 8, 0) == GEN ** 2
    assert l2(64, 8, 0) == GEN ** 6
    a = l2(65, 8, 0)
    assert a == GEN ** 7
    b = l2(2, 8, 3)
    assert b == GEN ** 3
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
