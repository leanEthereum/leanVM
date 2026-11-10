# expect: compile-error
# A range bound of 0 admits nothing (and g^(k-1) would be g^(-1)): the compiler must refuse it rather than emit a
# gadget whose complement wraps.
from snark_lib import *


def main():
    x = GEN
    assert log(x) < 0
    return
