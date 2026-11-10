# expect: exec-fail witness stream `r` exhausted
# witness r: 3
# witness r: 5
# Pops a two-entry stream three times, the third in a loop body: the third pop must fail rather than repeat an entry
# or yield zero.
from snark_lib import *


def main():
    a = hint_witness("r")
    b = hint_witness("r")
    assert a + b == 6
    for i in mul_range(1, GEN):
        c = hint_witness("r")
        assert c == 0
    return
