# expect: exec-fail write-once conflict
# public_input: 0, 0
# A false assert after a join, duplicated in the untaken arm: if the lowering shared the arm's instruction the check
# after the join would vanish and a false program would prove. It must fail.
from snark_lib import *

def main():
    hb = HeapBuf(2)
    hb[1] = GEN ** 3
    hb[GEN] = GEN ** 5
    a = hb[1]
    b = hb[GEN]
    if a == b:
        assert a == b
        hb[1] = GEN ** 3
    assert a == b
    return
