# expect: ok
# public_input: 0, 0
# witness x: GEN ** 4
# witness bad: 7
# The documented match hazard as an attacker uses it: an unchecked hinted scrutinee indexes past its 2-slot table
# into the next match's last slot, and the jump skips the failing assert b == 8 entirely. A program bug; pinned so a
# layout change that moves the hijack is noticed. match_checked_scrutinee is the fixed twin.
from snark_lib import *

def main():
    x = hint_witness("x")
    r = match(log(x), range(0, 2), lambda j: j * GEN)
    b = hint_witness("bad")
    assert b == 8
    y = GEN
    s = match(log(y), range(0, 3), lambda j: j * GEN ** 2)
    return
