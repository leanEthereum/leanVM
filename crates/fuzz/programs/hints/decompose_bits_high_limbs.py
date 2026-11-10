# expect: ok
# public_input: 1, 1
# hint_decompose_bits at nbits 192 over a word with all three limbs set: bits 64.. and 128.. come from the second and
# third limbs, so each limb's lowest bit and the word's top bit must land where the limb split says.
from snark_lib import *


def main():
    bits = StackBuf(192)
    w = f192(1, 1, 9223372036854775809)
    hint_decompose_bits(bits, w, 192)
    assert bits[0] == 1
    assert bits[1] == 0
    assert bits[64] == 1
    assert bits[65] == 0
    assert bits[128] == 1
    assert bits[190] == 0
    assert bits[191] == 1
    p = GEN ** 0
    p[1] = bits[128]
    p[GEN] = bits[191]
    return
