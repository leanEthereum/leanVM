# A `main` over the guest's helpers (crates/aggregation/src/tests.rs, `guest_snippet`), compiled by
# the Lean back end with them at the guest's placeholders (`lake exe guest-backend export snippets`).
def main():
    byte_bits = HeapBuf(SP_BYTE_VALUES)
    for v in unroll(0, SP_BYTE_VALUES):
        byte_bits[GEN ** v] = v
    r0, r1, z = da_verify(byte_bits)
    digest = StackBuf(2)
    keccak([r0, r1], [z, 0], digest)
    public = GEN ** 0
    assert public[1] == digest[0]
    assert public[GEN] == digest[1]
    return
