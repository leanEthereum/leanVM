# expect: ok
# public_input: 777, 31
# The same lazily-set constant across a skipped branch, in main's frame, where fp is the fixed g^0 and the jump
# tables live: the constant used after the join must still be written on the skipping path.
from snark_lib import *


def main():
    x = GEN ** 2
    r = HeapBuf(2)
    if x == GEN:
        r[1] = 777
        r[GEN] = 31
    else:
        r[GEN] = 31
    r[1] = 777
    p = GEN ** 0
    p[1] = r[1]
    p[GEN] = r[GEN]
    return
