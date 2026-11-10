# expect: ok
# Links an unwritten heap cell to a frame cell with a DEREF, then gives the frame cell its value with an assert; a
# second, independent read of the heap cell must see that value, or two names of one cell disagree.
# public_input: 11, 11
from snark_lib import *


def main():
    hb = HeapBuf(2)
    x = hb[GEN]
    assert 11 == x
    j = GEN ** 0
    y = hb[j * GEN]
    p = GEN ** 0
    p[1] = x
    p[GEN] = y
    return
