# expect: ok
# public_input: GEN ** 65536, 0
# witness n: GEN ** 65537
# witness x: GEN ** 65536
# A runtime bound just past 2^16 with the precheck omitted: x = g^65536 is below it, and its cell lies past the
# minimum memory, so the run grows the memory and the proof must agree the claim holds at 2^17 cells.
from snark_lib import *


def main():
    n = hint_witness("n")
    x = hint_witness("x")
    assert log(x) < log(n)
    p = GEN ** 0
    p[1] = x
    return
