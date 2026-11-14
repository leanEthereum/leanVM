# expect: ok
# Division of words with every limb set (outside K): the back-solved quotient times the divisor must give the
# dividend back exactly, and (a / b) / (a / b) is one.
from snark_lib import *


def main():
    a = 1 + 2 * 18446744073709551616 + 3 * 18446744073709551616 * 18446744073709551616
    b = 5 + 7 * 18446744073709551616
    q = a / b
    assert q * b == a
    r = b / a
    assert q * r == 1
    s = q / q
    assert s == 1
    return
