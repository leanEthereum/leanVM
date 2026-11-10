# expect: exec-fail (hint
# witness w: 6
# A hint into a cell the program already wrote with 5: the hint is a write like any other, so the different value must
# conflict, and the fault must name the hint that wrote it.
from snark_lib import *


def main():
    sb = StackBuf(2)
    sb[0] = 5
    hint_witness(sb[0:1], "w")
    return
