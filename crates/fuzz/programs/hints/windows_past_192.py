# expect: compile-error inside a 192-bit word
# Windows that run past bit 191 (start 190, two of width 4): the interpreter asserts the span fits the word. The compiler
# must refuse it, so the interpreter's assertion is never what stops it.
from snark_lib import *


def main():
    win = StackBuf(2)
    hint_windows_exponent(win, 5, 190, 4, 2)
    return
