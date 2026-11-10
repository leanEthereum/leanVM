# expect: ok
# public_input: GEN ** 15, GEN ** 1
# hint_windows_exponent over a word whose windows straddle the limb boundaries (bits 60..68 and 124..132), and at a
# nonzero `at`: each window arrives as g^n, range-checked and compared with the bits the literal spells.
from snark_lib import *


def main():
    w = f192(17293822569102704640, 1152921504606846991, 1)
    win = StackBuf(5)
    hint_windows_exponent(win, w, 60, 4, 2, 0)
    hint_windows_exponent(win, w, 124, 4, 2, 2)
    hint_windows_exponent(win, w, 128, 1, 1, 4)
    assert log(win[0]) < 16
    assert log(win[1]) < 16
    assert win[0] == GEN ** 15
    assert win[1] == GEN ** 15
    assert win[2] == GEN ** 1
    assert win[3] == GEN ** 1
    assert win[4] == GEN
    p = GEN ** 0
    p[1] = win[0]
    p[GEN] = win[4]
    return
