/-
  LeanVM.Guest.B1.Bits.Meaning

  The interface of B1's bit, log and exponent functions: what each computes, and the statement
  that its core IR computes it.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.ExpTables

/-!
# Bits, logs and the exponent: meanings (TRIAGE G #2, #16-21)

For each function of the guest (`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM
`40f877dc`, G below) its meaning `Meaning…` on its argument and return words, and `…_Spec`, the
statement that its core IR relation (`coreProgram.Rel`) is that meaning. A `…_Spec` is a
definition (a `Prop`); its proof is the theorem `…_holds : …_Spec` of the family's modules.

| function | G | meaning |
| --- | --- | --- |
| `assert_canonical` | 493-501 | `IsCanonical128` |
| `exponent_tables` | 717-742 (40f877dc) | `ExpTables`: squares, nibble shares, rank keys, groups' sides |
| `g_power_of_word` | 745-758 (40f877dc) | `v = E(n)`, `n < 64`, returns `g^n` |
| `assert_small_g_power` | 761-776 (40f877dc) | `x = g^e`, `e < 2^36` |
| `log2_ceil_in_the_exponent` | 779-794 (40f877dc) | the hinted `L` within its two bounds; `max floor (log2Ceil N)` (V:661) on `g^N` |
| `grind_check` | 781-807 | `powOk` (V:427): the low `bits` bits of the first limb are zero |

The range checks (`assert_small_g_power`, `log2_ceil_in_the_exponent`) are stated on a memory
image of at most `2^32` words (`rangeCheck_iff`), the table read being present (`ExpTables`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `assert_canonical` (G:558-565, TRIAGE #2) -/

/-- **`assert_canonical(word)`**: the word has no `y²` term; it returns `0`. -/
def MeaningAssertCanonical : List E → List E → Prop
  | [w], rets => IsCanonical128 w ∧ rets = [0]
  | _, _ => False

/-- `assert_canonical`'s core IR is its meaning. -/
def assert_canonical_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "assert_canonical" args rets ↔ MeaningAssertCanonical args rets

/-! ## `exponent_tables` (lean_ethereum.py:717-742) -/

/-- **`exponent_tables()`**: it returns a pointer holding the exponent table (`ExpTables`). -/
def MeaningExponentTables (rd : Reader) : List E → List E → Prop
  | [], [q] => ExpTables rd q
  | _, _ => False

/-- `exponent_tables`' core IR is its meaning. -/
def exponent_tables_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "exponent_tables" args rets ↔ MeaningExponentTables rd args rets

/-! ## `g_power_of_word` (lean_ethereum.py:745-758) -/

/-- **`g_power_of_word(value)`**: the value is the integer `n < 2^6` (`E(n)`), and the function
returns `g^n`. -/
def MeaningGPowerOfWord : List E → List E → Prop
  | [v], rets => ∃ n < 2 ^ 6, v = eOfNat n ∧ rets = [gen ^ n]
  | _, _ => False

/-- `g_power_of_word`'s core IR is its meaning. -/
def g_power_of_word_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "g_power_of_word" args rets ↔ MeaningGPowerOfWord args rets

/-! ## `assert_small_g_power` (lean_ethereum.py:761-776) -/

/-- **`assert_small_g_power(x, g_squares)`**: `x = g^e` with `e < 2^36` (nine hinted nibbles,
each range checked below `16`, their shares multiplied over the table); it returns nothing. -/
def MeaningAssertSmallGPower : List E → List E → Prop
  | [x, _], rets => (∃ e < 2 ^ 36, x = gen ^ e) ∧ rets = []
  | _, _ => False

/-- `assert_small_g_power`'s core IR is its meaning, on a memory image of `2^κ` words,
`6 ≤ κ ≤ 32`, holding the exponent table. -/
def assert_small_g_power_Spec : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → 6 ≤ κ → ∀ (L : MemoryImage κ) (x q : E), ExpTables L.read q →
    ∀ rets : List E, coreProgram.Rel L.read "assert_small_g_power" [x, q] rets ↔
      MeaningAssertSmallGPower [x, q] rets

/-! ## `log2_ceil_in_the_exponent` (lean_ethereum.py:779-794) -/

/-- **`log2_ceil_in_the_exponent(g_N, g_squares, floor, 34)`**: the hinted `L`, `floor ≤ L < 34`,
pinned by `g^(2^L) / g_N = g^e` and, above the floor, `g_N / g^(2^(L-1) + 1) = g^e'`, both
exponents below `2^36` (`assert_small_g_power`); it returns `g^L`. On `g_N = g^N`, `N` small,
`L` is `max floor (log2Ceil N)` (V:661; `meaningLog2CeilExp_pow`). -/
def MeaningLog2CeilExp (fl : ℕ) : List E → List E → Prop
  | [gN, _], rets =>
      ∃ L, fl ≤ L ∧ L < 34 ∧ (∃ e < 2 ^ 36, gen ^ 2 ^ L = gN * gen ^ e) ∧
        (L ≠ fl → ∃ e < 2 ^ 36, gN = gen ^ (2 ^ (L - 1) + 1 + e)) ∧ rets = [gen ^ L]
  | _, _ => False

/-- `log2_ceil_in_the_exponent__L{fl}_L34`'s core IR is its meaning, on a memory image of `2^κ`
words, `6 ≤ κ ≤ 32`, holding the exponent table. -/
def log2_ceil_in_the_exponent_Spec (name : String) (fl : ℕ) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → 6 ≤ κ → ∀ (L : MemoryImage κ) (gN q : E), ExpTables L.read q →
    ∀ rets : List E, coreProgram.Rel L.read name [gN, q] rets ↔ MeaningLog2CeilExp fl [gN, q] rets

/-- The deployed specializations: floors `0` and `15`, 34 bits. -/
def log2_Spec : Prop :=
  log2_ceil_in_the_exponent_Spec "log2_ceil_in_the_exponent__L0_L34" 0 ∧
    log2_ceil_in_the_exponent_Spec "log2_ceil_in_the_exponent__L15_L34" 15

/-! ## `grind_check` (G:912-938, TRIAGE #21) -/

/-- **`grind_check(word, bits)`** (`bits > 0`): the word, the first cell of the permutation the
nonce's challenge comes from, is canonical and the low `bits` bits of its first limb are zero:
`powOk bits` (V:427) of a challenge whose first limb is the word's (`challengeOf_limb0`). -/
def MeaningGrindCheck (bits : ℕ) : List E → List E → Prop
  | [w], rets => rets = [] ∧ IsCanonical128 w ∧ (w.limb 0).lane.toNat % 2 ^ bits = 0
  | _, _ => False

/-- `grind_check__L17`'s core IR is its meaning (`Whir.queryGrindingBits = 17`). -/
def grind_check_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "grind_check__L17" args rets ↔ MeaningGrindCheck 17 args rets

end
end LeanVM.Guest.B1
