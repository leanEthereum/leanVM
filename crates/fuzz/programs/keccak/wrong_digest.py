# expect: exec-fail write-once conflict
# A digest cell pre-written one bit off the true Keccak-256 of the message: the keccak statement becomes an
# assertion, and must fail. A verifier that let this run would accept forged signatures.
from snark_lib import *


def main():
    out = StackBuf(2)
    out[0] = 76870798587041994854595358325668108628
    out[1] = 156543651484862875866541738639399140452
    keccak([242716439218147592190247776532461068291, 178663287798046340062194692478498369747], [114610156739272160164435410271743099043, 50562197615718748928369898115721695347], out)
    return
