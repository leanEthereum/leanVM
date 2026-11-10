# expect: compile-error
# Indirect recursion through @inline functions would expand forever: the compiler must reject it instead of
# overflowing its stack.
from snark_lib import *


@inline
def a(x):
    return b(x) * GEN


@inline
def b(x):
    return a(x) * GEN


def main():
    r = a(1)
    return
