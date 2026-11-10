# expect: ok
# public_input: GEN ** 4, 9
# Reads the statement back and branches on it: a read of cell 0 after the publish must see the published value,
# and the branch taken must be the one the statement selects.
from snark_lib import *

def main():
    p = GEN ** 0
    x = GEN ** 2
    p[1] = x * x
    r = HeapBuf(1)
    if p[1] == GEN ** 4:
        r[1] = 9
    else:
        r[1] = 10
    p[GEN] = r[1]
    assert p[GEN] == 9
    return
