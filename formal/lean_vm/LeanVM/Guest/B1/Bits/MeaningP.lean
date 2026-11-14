/-
  LeanVM.Guest.B1.Bits.MeaningP

  The interface of B1's bit, log and exponent functions, stated for any program: what each
  computes, and that a program's relation at the function's name is it. No guest data.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.ExpTables

/-!
# Bits, logs and the exponent: meanings (TRIAGE G #16-21)

For each function of the guest (`crates/rec_aggregation/guests/lean_ethereum.py`, G below) its
meaning `Meaning…` on its argument and return words, and `…_SpecP P`, the statement that program
`P`'s relation at the function's name is that meaning. The proof of `…_SpecP P` (`…_holdsP`)
holds for every `P` that finds the function (`Finds`) and imports that function's core module
only; `Meaning.lean` states `…_Spec` at `coreProgram`.

| function | meaning |
| --- | --- |
| `exponent_tables` | `ExpTables`: squares, nibble shares, rank keys, groups' sides; `ExpWinTab`: the bit windows |
| `g_power_of_word` | 748-761 | `v = E(n)`, `n < 64`, returns `g^n` |
| `assert_small_g_power` | 764-779 | `x = g^e`, `e < 2^36` |
| `log2_ceil_in_the_exponent` | 782-797 | the hinted `L` within its two bounds; `max floor (log2Ceil N)` on `g^N` |
| `grind_check__L{bits}` | `powOk`: the low `bits` bits of the word's low limb (the permutation's lane `2`) are zero |

The range checks (`assert_small_g_power`, `log2_ceil_in_the_exponent`, `grind_check`'s windows)
are stated on a memory image of at most `2^32` words (`rangeCheck_iff`), the table read being
present (`ExpTables`, `WinTabs`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `exponent_tables` (lean_ethereum.py) -/

/-- **`exponent_tables()`**: it returns a pointer holding the exponent table (`ExpTables`) and its
bit windows (`ExpWinTab`, read as `WinTabs` at `q·g^236`, `winTabs_of_expWinTab`). -/
def MeaningExponentTables (rd : Reader) : List E → List E → Prop
  | [], [q] => ExpTables rd q ∧ ExpWinTab rd q
  | _, _ => False

/-- `P`'s relation at `exponent_tables` is its meaning. -/
def exponent_tables_SpecP (P : Program) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    P.Rel rd "exponent_tables" args rets ↔ MeaningExponentTables rd args rets

/-! ## `g_power_of_word` (lean_ethereum.py) -/

/-- **`g_power_of_word(value)`**: the value is the integer `n < 2^6` (`E(n)`), and the function
returns `g^n`. -/
def MeaningGPowerOfWord : List E → List E → Prop
  | [v], rets => ∃ n < 2 ^ 6, v = eOfNat n ∧ rets = [gen ^ n]
  | _, _ => False

/-- `P`'s relation at `g_power_of_word` is its meaning. -/
def g_power_of_word_SpecP (P : Program) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    P.Rel rd "g_power_of_word" args rets ↔ MeaningGPowerOfWord args rets

/-! ## `assert_small_g_power` (lean_ethereum.py) -/

/-- **`assert_small_g_power(x, g_squares)`**: `x = g^e` with `e < 2^36` (nine hinted nibbles,
each range checked below `16`, their shares multiplied over the table); it returns nothing. -/
def MeaningAssertSmallGPower : List E → List E → Prop
  | [x, _], rets => (∃ e < 2 ^ 36, x = gen ^ e) ∧ rets = []
  | _, _ => False

/-- `P`'s relation at `assert_small_g_power` is its meaning, on a memory image of `2^κ` words,
`6 ≤ κ ≤ 32`, holding the exponent table. -/
def assert_small_g_power_SpecP (P : Program) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → 6 ≤ κ → ∀ (L : MemoryImage κ) (x q : E), ExpTables L.read q →
    ∀ rets : List E, P.Rel L.read "assert_small_g_power" [x, q] rets ↔
      MeaningAssertSmallGPower [x, q] rets

/-! ## `log2_ceil_in_the_exponent` (lean_ethereum.py) -/

/-- **`log2_ceil_in_the_exponent(g_N, g_squares, floor, 34)`**: the hinted `L`, `floor ≤ L < 34`,
pinned by `g^(2^L) / g_N = g^e` and, above the floor, `g_N / g^(2^(L-1) + 1) = g^e'`, both
exponents below `2^36` (`assert_small_g_power`); it returns `g^L`. On `g_N = g^N`, `N` small,
`L` is `max floor (log2Ceil N)` (`meaningLog2CeilExp_pow`). -/
def MeaningLog2CeilExp (fl : ℕ) : List E → List E → Prop
  | [gN, _], rets =>
      ∃ L, fl ≤ L ∧ L < 34 ∧ (∃ e < 2 ^ 36, gen ^ 2 ^ L = gN * gen ^ e) ∧
        (L ≠ fl → ∃ e < 2 ^ 36, gN = gen ^ (2 ^ (L - 1) + 1 + e)) ∧ rets = [gen ^ L]
  | _, _ => False

/-- `P`'s relation at `log2_ceil_in_the_exponent__L{fl}_L34` is its meaning, on a memory image of
`2^κ` words, `6 ≤ κ ≤ 32`, holding the exponent table. -/
def log2_ceil_in_the_exponent_SpecP (P : Program) (name : String) (fl : ℕ) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → 6 ≤ κ → ∀ (L : MemoryImage κ) (gN q : E), ExpTables L.read q →
    ∀ rets : List E, P.Rel L.read name [gN, q] rets ↔ MeaningLog2CeilExp fl [gN, q] rets

/-- The deployed specializations: floors `0` and `16`, 34 bits. -/
def log2_SpecP (P : Program) : Prop :=
  log2_ceil_in_the_exponent_SpecP P "log2_ceil_in_the_exponent__L0_L34" 0 ∧
    log2_ceil_in_the_exponent_SpecP P "log2_ceil_in_the_exponent__L16_L34" 16

/-! ## `grind_check` (TRIAGE #21) -/

/-- **`grind_check(word, tabs, bits)`** (`0 < bits < 64`): the low `bits` bits of the word's low
limb are zero. The word is cell `1` of the permutation that absorbed a nonce, so its low limb is
that permutation's lane `2`, the proof of work (`powOk`, `Keccak.powLane_cells`, `grindOk_iff`). -/
def MeaningGrindCheck (bits : ℕ) : List E → List E → Prop
  | [w, _], rets => rets = [] ∧ (w.limb 0).lane.toNat % 2 ^ bits = 0
  | _, _ => False

/-- `P`'s relation at `grind_check__L{bits}` is its meaning, on a memory image of `2^κ` words,
`11 ≤ κ ≤ 32`, whose `tabs` holds the bit windows. -/
def grind_check_SpecP (P : Program) (bits : ℕ) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → winTabBits ≤ κ → ∀ (L : MemoryImage κ) (w tabs : E), WinTabs L.read tabs →
    ∀ rets : List E, P.Rel L.read (grindCheckName bits) [w, tabs] rets ↔
      MeaningGrindCheck bits [w, tabs] rets

/-- The grinds the deployed guest checks (`grind_check__L{bits}` in the core IR). -/
def grindBitsDeployed : List ℕ :=
  [2, 3, 7, 13, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]

/-- Every deployed `grind_check` is its meaning. -/
def grind_check_all_SpecP (P : Program) : Prop := ∀ bits ∈ grindBitsDeployed, grind_check_SpecP P bits

end
end LeanVM.Guest.B1
