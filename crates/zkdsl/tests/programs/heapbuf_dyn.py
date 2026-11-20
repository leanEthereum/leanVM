# Runtime-sized HeapBuf: the cell count is carried *in the exponent*: the
# buffer holds k cells where the size value is g^k. So a size derived from a
# runtime g-power is plain field arithmetic. Here a hinted count m = g^2 gives
# a buffer of m·m = g^4 = 4 cells; the four cells are filled from a witness
# stream and XOR-summed (`+` is XOR): 1^2^4^8 = 15. Published: (15, GEN ** 3).
# public_input: 15, GEN ** 3
# witness m: GEN ** 2
# witness vals: 1, 2, 4, 8
from snark_lib import *


def main():
    mb = StackBuf(1)
    hint_witness(mb[0:1], "m")
    m = mb[0]
    buf = HeapBuf(m * m)  # runtime size in the exponent: g^2 · g^2 = g^4 = 4 cells
    hint_witness(buf[0:4], "vals")
    s = buf[1] + buf[GEN] + buf[GEN ** 2] + buf[GEN ** 3]
    p = GEN ** 0
    p[1] = s
    p[GEN] = GEN ** 3
    return
