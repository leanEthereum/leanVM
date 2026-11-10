# expect: ok
# public_input: 7, 340282366920938463463374607431768211455
# `const(...)` in value position reads integers: subtraction, floor division and modulus that have no field meaning,
# and an integer sum at the 128-bit top. A wrong regime would publish different words.
from snark_lib import *

TOP = 340282366920938463463374607431768211455


def main():
    a = const(10 - 3)
    b = const(29 // 4 % 8)
    assert a == b
    c = const(TOP - 1 + 1)
    p = GEN ** 0
    p[1] = a
    p[GEN] = c
    return
