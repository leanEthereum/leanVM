# expect: exec-fail failed range check
# public_input: 0, 0
# witness x: GEN ** 4
# witness bad: 7
# match_unchecked_scrutinee_hijack with the range check the doc requires: the hijacking scrutinee must now fail.
from snark_lib import *

def main():
    x = hint_witness("x")
    assert log(x) < 2
    r = match(log(x), range(0, 2), lambda j: j * GEN)
    b = hint_witness("bad")
    assert b == 8
    y = GEN
    s = match(log(y), range(0, 3), lambda j: j * GEN ** 2)
    return
