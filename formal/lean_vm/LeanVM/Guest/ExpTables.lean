/-
  LeanVM.Guest.ExpTables

  The exponent table `exponent_tables` fills (`B1.ExpTables`), for the guest's shared check
  context (`Glob`) and B1's meaning of `exponent_tables` (`B1/Bits/Meaning.lean`).
-/

module

public import LeanVM.Guest.Core
public import Statement.Field
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts

/-!
# The exponent table

Defined here, apart from B1's proofs, so that the check context, and with it the kernel-checked
certificates of the compiled functions (`B2C`), do not import them.

`exponent_tables()` (`lean_ethereum.py`) fills one read-only `HeapBuf(WIN_TAB_AT + WIN_TAB_LEN)`,
`178 + 2048` words, indexed by g-powers, in three sections:

| offsets | words | readers |
| --- | --- | --- |
| `j < 34` | `g^(2^j)` | `log2_ceil_in_the_exponent`, `verify_sub` |
| `34 + 16 j + u`, `j < 9`, `u < 16` | `g^(u·16^j)`, the nibble shares | `assert_small_g_power` |
| `178 + n`, `n < 2^11` | `E(n)`, a bit window's pattern | `grind_check`, `query_window` (`WinTabs`, at `q·g^178`) |
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `SIZE_BITS`: the squares' section's length. -/
abbrev sizeBits : ℕ := guest_const% SIZE_BITS

/-- `SEL_TAB_NIBBLES = (SIZE_BITS + 3) // 4` (`lean_ethereum.py`). -/
abbrev selTabNibbles : ℕ := 9

/-- **The exponent table at `q`** (`exponent_tables`, `lean_ethereum.py`): the squares
`q[g^j] = g^(2^j)`, `j < 34`, and the nibble shares `q[g^(34 + 16j + u)] = g^(u·16^j)`, `j < 9`,
`u < 16`. -/
def ExpTables (rd : Reader) (q : E) : Prop :=
  (∀ j < sizeBits, LoadHolds rd q j (gen ^ 2 ^ j)) ∧
    (∀ j < selTabNibbles, ∀ u < 16, LoadHolds rd q (sizeBits + 16 * j + u) (gen ^ (u * 16 ^ j)))

/-- `WIN_TAB_BITS`: the width of a bit window the table covers. -/
abbrev winTabBits : ℕ := guest_const% WIN_TAB_BITS

/-- `WIN_TAB_AT = SIZE_BITS + 16 SEL_TAB_NIBBLES`: where the bit-window table starts. -/
abbrev winTabAt : ℕ := guest_const% WIN_TAB_AT

/-- **The bit-window table at `tabs`** (`exponent_tables`' last section, read as `tabs[w]` with
`tabs = g_squares * GEN ** WIN_TAB_AT`): the word at `tabs·g^n` is the integer `n`, for every
`n < 2^11`. `grind_check` and `query_window` take it as a hypothesis on their `tabs`. -/
def WinTabs (rd : Reader) (tabs : E) : Prop :=
  ∀ n < 2 ^ winTabBits, LoadHolds rd tabs n (eOfNat n)

/-- The window section of the exponent table at `q`. -/
def ExpWinTab (rd : Reader) (q : E) : Prop :=
  ∀ n < 2 ^ winTabBits, LoadHolds rd q (winTabAt + n) (eOfNat n)

end
end LeanVM.Guest.B1
