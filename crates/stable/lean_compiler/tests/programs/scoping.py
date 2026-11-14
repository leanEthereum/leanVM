# Pins the scoping semantics: bindings (and compile-time index constants)
# made inside a branch are local to it, and the lazily-cached range-check
# constant cells revert at the join. The not-taken branch below materializes
# a bound-16 cell that must NOT leak to the check after the join: a leak
# would read an unwritten cell and fail witness generation loudly.
# Published: (9, 6).
# public_input: 9, 6
from snark_lib import *


def main():
    x = GEN ** 3
    assert log(x) < 8  # bound-8 cell cached in main
    v = 5
    k = 2
    if x == GEN ** 3:
        v = 7  # branch-local rebinding
        assert v == 7
        assert log(x) < 8  # reuses the pre-branch bound-8 cell
    assert v == 5  # the outer binding is untouched at the join
    if x != GEN ** 3:
        k = x  # (not taken) kills k's const-ness: locally only
        assert log(x) < 16  # (not taken) caches bound-16 inside the branch
    sb = StackBuf(4)
    sb[k] = 9  # k is still the compile-time 2
    assert log(x) < 16  # must re-materialize its bound cell after the join
    y = 3
    y = y * GEN  # rebinding reads the old binding: 3·g = 6
    assert y == 6
    p = GEN ** 0
    p[1] = sb[2]
    p[GEN] = y
    return
