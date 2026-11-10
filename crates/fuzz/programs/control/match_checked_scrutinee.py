# expect: exec-fail not a small g-power
# witness x: GEN ** 4
# The same out-of-range scrutinee, range-checked first as the doc requires: the check must fault before the dispatch
# reads past the table.
from snark_lib import *


def main():
    x = hint_witness("x")
    assert log(x) < 4
    r = match(log(x), range(0, 4), lambda k: k * 2 + 1)
    p = GEN ** 0
    p[1] = r
    return
