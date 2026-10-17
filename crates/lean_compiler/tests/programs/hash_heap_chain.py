# Runtime slices: `buf[i:i + 2]` with a runtime g-power index `i` names the
# heap cells `buf·i·g^k`, k < 2 (one MUL folds `i` into the pointer). A SHA3
# chain over heap pairs (256-bit SHA3 digest = two canonical cells),
# addressed by the loop counter: value k sits at cells g^{2k}..g^{2k+1}, and
# value k+1 = H(value k, value k). Published: the two 128-bit digest cells of
# H^3(5, 7).
# public_input: 27240554859721455327970068208906002034, 119514610692047185288834508057685931752
from snark_lib import *


def main():
    buf = HeapBuf(8)
    buf[1] = 5
    buf[GEN] = 7
    for i in mul_range(1, GEN ** 3):
        b = i * i  # value k at cells g^{2k}..g^{2k+1}
        sha3(buf[b:b + 2], buf[b:b + 2], buf[b * GEN ** 2:b * GEN ** 2 + 2])
    p = GEN ** 0
    p[1] = buf[GEN ** 6]
    p[GEN] = buf[GEN ** 7]
    return
