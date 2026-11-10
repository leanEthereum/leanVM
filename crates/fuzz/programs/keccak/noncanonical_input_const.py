# expect: exec-fail not a canonical 128-bit embedding
# A keccak input word with a nonzero top limb: the hash reads 128-bit cells, so the run must refuse the word instead
# of hashing its low 128 bits, which would let two different words share a digest.
from snark_lib import *


def main():
    w = f192(1, 0, 1)
    out = StackBuf(2)
    keccak([w, 0], [0, 0], out)
    return
