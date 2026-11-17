# The verifiers' fixture program (`fixture.rs`) and the chain cases of
# `formal/lean_vm/scripts/export-rust.sh`: a two-block Keccak and a loop of field arithmetic, long
# enough that every table and the Keccak reduction are exercised. Compiled by the Lean back end at
# each step count `LOOP_STEPS_PLACEHOLDER` takes (`guest-export`'s `CHAIN_STEPS`, written to
# `crates/zkdsl_compiler/tests/suite/lean_backend/chain<steps>.txt`).
from snark_lib import *

LOOP_STEPS = LOOP_STEPS_PLACEHOLDER

def mix(value, tag):
    # A JUMP condition is K-valued (a g-power here), never an arbitrary word.
    if tag == 0:
        return value
    return value * GEN + value

def main():
    # 160 bytes: two blocks, the second read in the odd layout.
    digest = StackBuf(2)
    keccak_cells([5, 7, 5, 7, 5, 7, 5, 7, 5, 7], digest)

    chain = HeapBuf(LOOP_STEPS + 1)
    chain[1] = digest[0]
    for index in mul_range(1, GEN ** LOOP_STEPS):
        chain[index * GEN] = mix(chain[index] + index, index) + index

    public = GEN ** 0
    public[1] = chain[GEN ** LOOP_STEPS]
    public[GEN] = mix(digest[1], GEN ** 0)
    return
