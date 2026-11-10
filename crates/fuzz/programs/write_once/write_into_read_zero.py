# expect: exec-fail write-once conflict
# A keccak output cell is read (as zero) by arithmetic before the keccak writes it: the read froze the cell at zero,
# so the hash's write must conflict rather than leave the earlier product computed from a phantom zero.
from snark_lib import *


def main():
    out = StackBuf(2)
    early = out[0] * GEN
    keccak([1, 2], [3, 4], out)
    p = GEN ** 0
    p[1] = early
    return
