# expect: ok
# public_input: 270990084338373815782580257413909024812, GEN ** 7
# witness sig: 169656230059440237948422059626424781492, 32735715232830091225269252692726959127
# The forward forgery against a WOTS verifier WITHOUT the checksum chain: digit 7 signed from a signature of 6.
# It is accepted, which is the protocol's flaw and not the VM's; wots_forged_next_digit is the checksummed verifier.
from snark_lib import *


def main():
    p = GEN ** 0
    m = p[GEN]
    assert log(m) < 16
    sig = StackBuf(2)
    hint_witness(sig, "sig")
    buf = HeapBuf(34)
    buf[1] = sig[0]
    buf[GEN] = sig[1]
    steps = GEN ** 15 / m
    for i in mul_range(1, steps):
        b = i * i
        keccak(buf[b:b + 2], buf[b:b + 2], buf[b * GEN ** 2:b * GEN ** 2 + 2])
    e = steps * steps
    p[1] = buf[e]
    return
