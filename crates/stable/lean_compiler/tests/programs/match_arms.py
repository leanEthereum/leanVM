# `match(log(x), range(a, b), lambda i: …, …)`: a match with generated
# arms: arm j is the lambda body with i replaced by the integer literal j, and
# every arm writes its results into the same fresh cells (write-once: exactly
# one arm executes), bound to the assignment targets. Ranges are contiguous
# from 0. With x = GEN ** 3: shift(3) = 3·g = 6, and the second pair's
# two(3) = (3, 3·g) = (3, 6), so a + b = 3 + 6 = 5 (`+` is XOR).
# public_input: 6, 5
from snark_lib import *


def main():
    x = GEN ** 3
    r = match(log(x), range(0, 6), lambda i: shift(i))
    assert r == 6
    a, b = match(log(x), range(0, 2), lambda i: two(1), range(2, 6), lambda i: two(i))
    p = GEN ** 0
    p[1] = r
    p[GEN] = a + b
    return


def shift(v):
    return v * GEN


def two(v):
    return v, v * GEN
