# expect: ok
# public_input: 18446744073709551616, 27
# The literal 2^64 is the tower element y, so y^3 + y = 1; `2 ** 64` in a value position is the field power x^64,
# which reduces to x^4 + x^3 + x + 1 = 27; `const(2 ** 64)` is y again. Any regime mixup breaks one of these.
from snark_lib import *


def main():
    y = 18446744073709551616
    assert y * y * y + y == 1
    z = 2 ** 64
    assert z == 27
    w = const(2 ** 64)
    assert w == y
    assert y * y == f192(0, 0, 1)
    p = GEN ** 0
    p[1] = w
    p[GEN] = z
    return
