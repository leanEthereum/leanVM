# expect: exec-fail write-once conflict
# `assert a != b` on two runtime values that are equal: x = a + b is zero, so x * inv is zero whatever inverse the
# prover hints, and the SET of 1 into that cell must conflict.
from snark_lib import *


def main():
    a = GEN ** 7
    b = GEN ** 3 * GEN ** 4
    assert a != b
    return
