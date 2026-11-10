# expect: ok
# public_input: 232515940305832244453259077493881403150, 104118072785224992633742327205763571547
# The doc's unenforced corner: len=1 but the message cell also holds 0x01 in byte 1, which cancels the padding byte.
# The circuit hashes the block (ff, 00, ..., 80), not Keccak-256 of 0xff; pinned so a change in what it computes shows.
from snark_lib import *


def main():
    out = StackBuf(2)
    keccak([511, 0], [0, 0], out, len=1)
    assert out[0] != 82924076288974562650078453474641844875
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
