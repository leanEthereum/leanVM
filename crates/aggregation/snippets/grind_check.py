# A `main` over the guest's helpers (crates/aggregation/src/tests.rs, `guest_snippet`), compiled by
# the Lean back end with them at the guest's placeholders (`lake exe guest-backend export snippets`).
def main():
    word = hint_witness("w")
    grind_check(word, exponent_tables() * GEN ** WIN_TAB_AT, 3)
    return
