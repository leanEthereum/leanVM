# expect: compile-error
# A compile-time bound past the largest memory size the gadget is sound for: it must be refused.
from snark_lib import *


def main():
    x = GEN
    assert log(x) < 1073741825
    return
