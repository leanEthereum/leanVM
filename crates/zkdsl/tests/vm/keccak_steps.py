# `STEPS` chained self-hashes of the cells `[5, 7]`: a KECCAK table of `STEPS` rows. Compiled by the Lean back end at
# each count `guest-export`'s `VM_TEMPLATES` gives `STEPS_PLACEHOLDER`, written to `tests/compiled/keccak_steps<count>.txt`.
from snark_lib import *

STEPS = STEPS_PLACEHOLDER

def main():
    h = StackBuf(2 * STEPS + 2)
    h[0] = 5
    h[1] = 7
    for i in unroll(0, STEPS):
        keccak(h[2 * i:2 * i + 2], h[2 * i:2 * i + 2], h[2 * i + 2:2 * i + 4])
    p = 1
    p[1] = h[2 * STEPS]
    p[GEN] = h[2 * STEPS + 1]
    return
