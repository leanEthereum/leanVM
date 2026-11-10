# expect: compile-error put the whole operand inside
# Python reads log(x) * 2 < 8 as 2 * log x, the compiler would read log(2x): rejected as ambiguous.
from snark_lib import *

def main():
    x = GEN ** 5
    assert log(x) * 2 < 8
    return
