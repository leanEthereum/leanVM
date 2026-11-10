# expect: exec-fail failed range check
# public_input: 264774187848096468789582432106039719637, GEN ** 16
# witness sig: 286311811352373539804301310312849626455, 302407041982570567765720831557540980620, 122577560455215414322804142105733466627, 30785314681611910104073856221681927947
# Digit 16, past W - 1: the range check must refuse it before the checksum wraps.
from snark_lib import *

# Two-chain WOTS over Keccak, W = 16: the message digit m is statement word 1, its checksum digit 15 - m signs the
# second chain, and the public key is the first digest cell of H(end1, end2) in statement word 0.


def chain(s0, s1, steps):
    buf = HeapBuf(34)
    buf[1] = s0
    buf[GEN] = s1
    for i in mul_range(1, steps):
        b = i * i
        keccak(buf[b:b + 2], buf[b:b + 2], buf[b * GEN ** 2:b * GEN ** 2 + 2])
    e = steps * steps
    return buf[e], buf[e * GEN]


def main():
    p = GEN ** 0
    m = p[GEN]
    assert log(m) < 16
    c = GEN ** 15 / m
    assert log(c) < 16
    sig = StackBuf(4)
    hint_witness(sig, "sig")
    e0, e1 = chain(sig[0], sig[1], GEN ** 15 / m)
    f0, f1 = chain(sig[2], sig[3], GEN ** 15 / c)
    pk = StackBuf(2)
    keccak([e0, e1], [f0, f1], pk)
    p[1] = pk[0]
    return
