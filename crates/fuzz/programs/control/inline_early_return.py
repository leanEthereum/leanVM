# expect: compile-error
# An @inline body must end in one top-level return; an early return inside an `if` must be refused, since inlined
# code has no frame to leave.
from snark_lib import *


@inline
def f(x):
    if x == 1:
        return 5
    return 7


def main():
    r = f(GEN)
    return
