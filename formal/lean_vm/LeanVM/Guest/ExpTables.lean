/-
  LeanVM.Guest.ExpTables

  The exponent table `exponent_tables` fills (`B1.ExpTables`), for the guest's shared check
  context (`Glob`) and B1's meaning of `exponent_tables` (`B1/Bits/Meaning.lean`).
-/

module

public import LeanVM.Guest.Core
public import Statement.Field

/-!
# The exponent table

Defined here, apart from B1's proofs, so that the check context, and with it the kernel-checked
certificates of the compiled functions (`B2C`), do not import them.

`exponent_tables()` (`lean_ethereum.py:717-742` at leanVM `40f877dc`) fills one read-only
`HeapBuf(SIDE_TAB_AT + N_BLOCK_GROUPS)`, `236` words, indexed by g-powers, in four sections:

| offsets | words | readers |
| --- | --- | --- |
| `j < 34` | `g^(2^j)` | `log2_ceil_in_the_exponent`, `verify_sub`, `certify_placement`, `da_row_shape` |
| `34 + 16 j + u`, `j < 9`, `u < 16` | `g^(u·16^j)`, the nibble shares | `assert_small_g_power`, `check_opening_terminal` |
| `178 + k`, `k < 34` | `g^(k·254)`, the rank keys | `verify_tables`, `certify_placement` |
| `212 + gi`, `gi < 24` | `E(s)`, block group `gi`'s side `s` | `verify_tables` |
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `SIZE_BITS`: the squares' section's length. -/
abbrev sizeBits : ℕ := 34

/-- `SEL_TAB_NIBBLES = (SIZE_BITS + 3) // 4` (`lean_ethereum.py:287`). -/
abbrev selTabNibbles : ℕ := 9

/-- `RANK_KEYS_AT = SIZE_BITS + 16 SEL_TAB_NIBBLES` (`lean_ethereum.py:289`). -/
abbrev rankKeysAt : ℕ := 178

/-- `RANK_STRIDE = N_BLOCKS + N_COMMITTED_COLS = 153 + 101` (`lean_ethereum.py:290`, deployed). -/
abbrev rankStride : ℕ := 254

/-- `SIDE_TAB_AT = RANK_KEYS_AT + SIZE_BITS` (`lean_ethereum.py:292`). -/
abbrev sideTabAt : ℕ := 212

/-- `SIDE_GROUP_START` (deployed): side `s`'s first bus block group, then `N_BLOCK_GROUPS = 24`. -/
def sideGroupStart : List ℕ := [0, 9, 18, 24]

/-- `N_GKR_SIDES`. -/
abbrev nGkrSides : ℕ := 3

/-- `N_BLOCK_GROUPS`. -/
abbrev nBlockGroups : ℕ := 24

/-- **The exponent table at `q`** (`exponent_tables`, `lean_ethereum.py:717-742`): the squares
`q[g^j] = g^(2^j)`, `j < 34`; the nibble shares `q[g^(34 + 16j + u)] = g^(u·16^j)`, `j < 9`,
`u < 16`; the rank keys `q[g^(178 + k)] = g^(k·254)`, `k < 34`; and each bus block group's side,
`q[g^(212 + gi)] = E(s)` for the groups `gi` of side `s`. -/
def ExpTables (rd : Reader) (q : E) : Prop :=
  (∀ j < sizeBits, LoadHolds rd q j (gen ^ 2 ^ j)) ∧
    (∀ j < selTabNibbles, ∀ u < 16, LoadHolds rd q (sizeBits + 16 * j + u) (gen ^ (u * 16 ^ j))) ∧
    (∀ k < sizeBits, LoadHolds rd q (rankKeysAt + k) (gen ^ (k * rankStride))) ∧
    (∀ s < nGkrSides, ∀ gi, sideGroupStart.getD s 0 ≤ gi → gi < sideGroupStart.getD (s + 1) 0 →
      LoadHolds rd q (sideTabAt + gi) (eOfNat s))

end
end LeanVM.Guest.B1
