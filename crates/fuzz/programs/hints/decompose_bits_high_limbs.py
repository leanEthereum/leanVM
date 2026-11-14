# expect: ok
# public_input: 0, 1
# hint_decompose_bits at nbits 128 over a word with both limbs set: bits 64.. come from the high limb, so each
# limb's lowest bit and the word's top bit must land where the limb split says.
from snark_lib import *


def main():
    bits = StackBuf(128)
    w = 1 + 9223372036854775809 * 18446744073709551616
    hint_decompose_bits(bits, w, 128)
    assert bits[0] == 1
    assert bits[1] == 0
    assert bits[64] == 1
    assert bits[65] == 0
    assert bits[126] == 0
    assert bits[127] == 1
    p = GEN ** 0
    p[1] = bits[65]
    p[GEN] = bits[127]
    return
