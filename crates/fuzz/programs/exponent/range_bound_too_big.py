# expect: compile-error
# A compile-time bound of 2^16 + 1 exceeds the minimum memory size the gadget is sound for: it must be refused.
from snark_lib import *


def main():
    x = GEN
    assert log(x) < 65537
    return
