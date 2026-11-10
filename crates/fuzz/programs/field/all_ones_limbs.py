# expect: ok
# public_input: 1, 0
# The all-ones word in every limb: its runtime inverse is back-solved, x + x vanishes on all 192 bits, and dividing
# by itself is one. A limb lost in the multiplier or in a SET of the literal breaks these.
from snark_lib import *


def main():
    a = f192(18446744073709551615, 18446744073709551615, 18446744073709551615)
    inv = 1 / a
    assert inv * a == 1
    assert a + a == 0
    q = a / a
    assert q == 1
    b = a * a
    c = b / a
    assert c == a
    p = GEN ** 0
    p[1] = q
    return
