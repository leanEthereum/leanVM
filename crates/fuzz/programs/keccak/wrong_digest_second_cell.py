# expect: exec-fail write-once conflict
# public_input: 76870798587041994854595358325668108629, 0
# Only the second digest cell is wrong (its top bit flipped) while the first is right and published: a check that
# compared one cell, or lost the high half of a cell, would accept.
from snark_lib import *


def main():
    out = StackBuf(2)
    out[0] = 76870798587041994854595358325668108629
    out[1] = 156543651484862875866541738639399140452 + 170141183460469231731687303715884105728
    p = GEN ** 0
    p[1] = out[0]
    keccak([242716439218147592190247776532461068291, 178663287798046340062194692478498369747], [114610156739272160164435410271743099043, 50562197615718748928369898115721695347], out)
    return
