# A `main` over the guest's helpers (crates/aggregation/src/tests.rs, `guest_snippet`), compiled by
# the Lean back end with them at the guest's placeholders (`lake exe guest-backend export snippets`).
def main():
    n_g = hint_witness("n")
    bigs, body, rest = list_split(n_g)
    public = GEN ** 0
    assert public[1] == body
    assert public[GEN] == rest
    return
