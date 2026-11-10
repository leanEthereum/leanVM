# expect: ok
# public_input: 5, 6
# A range check DEREFs through its operand, touching cell x: here x is a heap pointer whose cell is written only
# afterwards. The touch is back-filled at the end, so it must not conflict with the later legitimate store.
from snark_lib import *

def main():
    hb = HeapBuf(2)
    assert log(hb) < 65536
    assert_gpow(hb * GEN)
    hb[1] = 5
    hb[GEN] = 6
    p = GEN ** 0
    p[1] = hb[1]
    p[GEN] = hb[GEN]
    return
