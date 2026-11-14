# expect: exec-fail not a g-power below 2^28
# witness z: 0
# `assert_gpow(0)`: zero is no power of g at all, so the DEREF through it must fault as a wild pointer.
from snark_lib import *


def main():
    z = hint_witness("z")
    assert_gpow(z)
    return
