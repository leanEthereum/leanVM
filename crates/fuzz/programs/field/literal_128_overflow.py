# expect: compile-error
# An integer literal of 2^128 does not fit the 128-bit literal embedding: it must be refused, not truncated to zero or
# wrapped into the top limb.
from snark_lib import *


def main():
    x = 340282366920938463463374607431768211456
    p = GEN ** 0
    p[1] = x
    return
