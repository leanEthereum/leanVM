# expect: ok
# public_input: 5, 7
# witness w: 5, 7
# A hint into cells the program already wrote with the same values: the hint must agree as a no-op, so a program can
# pin advice by writing the expected value first.
from snark_lib import *


def main():
    sb = StackBuf(2)
    sb[0] = 5
    sb[1] = 7
    hint_witness(sb, "w")
    p = GEN ** 0
    p[1] = sb[0]
    p[GEN] = sb[1]
    return
