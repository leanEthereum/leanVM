# expect: exec-fail holds 3 values, the destination 2
# witness w: 1, 2, 3
# An entry of three values hinted into a two-cell run: the extra value must not spill into the next cell.
from snark_lib import *


def main():
    sb = StackBuf(3)
    hint_witness(sb[0:2], "w")
    sb[2] = 9
    return
