# expect: exec-fail write-once conflict
# public_input: 0, 0
# witness u: 3, 5, 7, 9
# witness w: GEN, GEN ** 2, GEN ** 3, GEN ** 4 + 18446744073709551616
# An honest witness except w3 carries a high limb, which shifts its product: the packing hashes the limb and the check must refuse.
from snark_lib import *

# The batch check u_i * w_i == t_i with its challenge drawn from Keccak over every hinted word (packed through the
# hinted high limb that KECCAK's canonical input pins): changing any hint changes the challenge.


@inline
def pack(x):
    limbs = StackBuf(2)
    hint_f128_limbs(limbs, x)
    assert_in_k(limbs[1], limbs[1])
    lo = x + 18446744073709551616 * limbs[1]
    return lo, limbs[1]


def main():
    u = StackBuf(4)
    hint_witness(u, "u")
    w = StackBuf(4)
    hint_witness(w, "w")
    cells = StackBuf(16)
    for i in unroll(0, 4):
        lo, hi = pack(u[i])
        cells[2 * i] = lo
        cells[2 * i + 1] = hi
        lo, hi = pack(w[i])
        cells[8 + 2 * i] = lo
        cells[8 + 2 * i + 1] = hi
    d = StackBuf(2)
    keccak_cells(cells, d)
    r = d[0]
    t = [6, 20, 56, 144]
    acc = 0
    rp = 1
    for i in unroll(0, 4):
        acc = acc + rp * (u[i] * w[i] + t[i])
        rp = rp * r
    assert acc == 0
    return
