# expect: ok
# public_input: 1, 0
# Mutual recursion on g-powers: even(g^n) and odd(g^n) call each other down to g^0. The parity of 37 must come out
# odd, which needs every frame's return value to land in its caller's cell.
from snark_lib import *


def even(x):
    if x == 1:
        return 1
    r = odd(x / GEN)
    return r


def odd(x):
    if x == 1:
        return 0
    r = even(x / GEN)
    return r


def main():
    a = odd(GEN ** 37)
    b = even(GEN ** 37)
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
