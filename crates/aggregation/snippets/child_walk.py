# A `main` over the guest's helpers (crates/aggregation/src/tests.rs, `guest_snippet`), compiled by
# the Lean back end with them at the guest's placeholders (`lake exe guest-backend export snippets`).
def main():
    n_c = hint_witness("n")
    table = HeapBuf(GEN ** 8)
    hint_witness(table[0:8], "claims")
    cover = HeapBuf(GEN ** 2)
    d0, d1 = child_claim_list_digest(table, cover, GEN ** 3, GEN ** 2, n_c)
    public = GEN ** 0
    assert public[1] == d0
    assert public[GEN] == d1
    return
