# expect: ok
# public_input: 1, 0
# `assert a != b` inside a skipped branch and again after the join: its SET of 1 and hinted inverse must not be shared
# across the join, or the second assertion reads an unwritten cell on the skipping path.
from snark_lib import *


def f(a, b, c):
    if c == 1:
        assert a != b
    assert a != b
    assert a == a
    return 1


def main():
    u = f(GEN, GEN ** 2, 0)
    v = f(GEN, GEN ** 2, 1)
    p = GEN ** 0
    p[1] = u * v
    return
