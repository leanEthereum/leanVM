# expect: exec-fail write-once conflict
# public_input: 0, 0
# assert a != b uses a hinted inverse and a pooled 1 cell: duplicated in an untaken arm, the check after the join must
# still run its own three instructions and fail on equal operands.
from snark_lib import *

def main():
    hb = HeapBuf(2)
    hb[1] = GEN ** 3
    hb[GEN] = GEN ** 3
    a = hb[1]
    b = hb[GEN]
    if a == GEN:
        assert a != b
    assert a != b
    return
