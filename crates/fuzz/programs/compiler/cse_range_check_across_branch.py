# expect: exec-fail failed range check
# public_input: 0, 0
# A failing range check after a join whose twin sits in the untaken arm, and whose bound cell the arm materialized:
# neither the check nor its bound may be shared past the join.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = GEN ** 9
    c = hb[1]
    if c == GEN:
        assert log(c) < 4
    assert log(c) < 4
    return
