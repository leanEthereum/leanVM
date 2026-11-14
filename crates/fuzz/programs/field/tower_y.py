# expect: ok
# public_input: 18446744073709551616, 27
# The literal 2^64 is the tower element y, so y^2 = xy + 1, the word with low limb 1 and high limb x = 2;
# `2 ** 64` in a value position is the field power x^64, which reduces to x^4 + x^3 + x + 1 = 27;
# `const(2 ** 64)` is y again. Any regime mixup breaks one of these.
from snark_lib import *


def main():
    y = 18446744073709551616
    assert y * y == 1 + 2 * 18446744073709551616
    z = 2 ** 64
    assert z == 27
    w = const(2 ** 64)
    assert w == y
    assert y * y == 36893488147419103233
    p = GEN ** 0
    p[1] = w
    p[GEN] = z
    return
