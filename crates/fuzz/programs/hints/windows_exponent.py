# expect: ok
# public_input: GEN ** 15, GEN ** 1
# hint_windows_exponent over a word whose windows straddle the limb boundary (bits 60..67) and reach the word's
# top (bit 124..127), and at a nonzero `at`: each window arrives as g^n, range-checked and compared with the bits
# the literal spells.
from snark_lib import *


def main():
    w = 17293822569102704640 + 1152921504606846991 * 18446744073709551616
    win = StackBuf(3)
    hint_windows_exponent(win, w, 60, 4, 2, 0)
    hint_windows_exponent(win, w, 124, 4, 1, 2)
    assert log(win[0]) < 16
    assert log(win[1]) < 16
    assert win[0] == GEN ** 15
    assert win[1] == GEN ** 15
    assert win[2] == GEN ** 1
    p = GEN ** 0
    p[1] = win[0]
    p[GEN] = win[2]
    return
