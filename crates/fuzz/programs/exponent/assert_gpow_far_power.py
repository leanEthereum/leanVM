# expect: exec-fail not a g-power below 2^28
# witness z: 5
# 5 = 1 + x^2 is a nonzero element of K, so a power of g, but its exponent is astronomically large: `assert_gpow`
# must reject it as outside the memory, or a "g-power" check proves nothing.
from snark_lib import *


def main():
    z = hint_witness("z")
    assert_gpow(z)
    return
