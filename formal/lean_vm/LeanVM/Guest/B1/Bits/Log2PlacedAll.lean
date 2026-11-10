/-
  LeanVM.Guest.B1.Bits.Log2PlacedAll

  The deployed specializations of `log2_ceil_in_the_exponent` (floors `0` and `15`), placed and
  bounded, and their `CompleteAtD` / `CompleteAtDTB` forms.
-/

module

public import LeanVM.Guest.B1.Bits.Log2Placed

/-!
# `log2_ceil_in_the_exponent__L{0,15}_L34`, placed

For `6 ≤ κ`, `N < 2^34` and `L = max fl (log2Ceil N) < 34`: on `g^N` and the exponent table
(`log2Lin sqE`), `log2_ceil_in_the_exponent__L{fl}_L34` returns `g^L` within
`fs name + 34 + 2 · fs "assert_small_g_power"` words (`log2_L0_completeAtB`,
`log2_L15_completeAtB`); without the bound (`…_completeAt`, `CompleteAtD`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen log2Ceil)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem loop_lce_L0 : coreProgram.loop "log2_ceil_in_the_exponent__L0_L34" = false := by
  rw [Program.loop_of_find? find_lce_L0]; decide +kernel

theorem loop_lce_L15 : coreProgram.loop "log2_ceil_in_the_exponent__L15_L34" = false := by
  rw [Program.loop_of_find? find_lce_L15]; decide +kernel

/-- **`log2_ceil_in_the_exponent__L0_L34`, placed and bounded.** -/
theorem log2_L0_completeAtB (κ : ℕ) (hκ6 : 6 ≤ κ) (N sqE : ℕ) (hN : N < 2 ^ 34)
    (hL : max 0 (log2Ceil N) < 34) :
    CompleteAtB fs cert κ "log2_ceil_in_the_exponent__L0_L34" (log2Lin sqE)
      [gen ^ N, ofK (Parameters.addressOfIndex sqE)] (Returns [gen ^ max 0 (log2Ceil N)])
      (fs "log2_ceil_in_the_exponent__L0_L34" + 34 + 2 * fs "assert_small_g_power") :=
  lce_completeAtB 0 (by norm_num) find_lce_L0 rfl core301_body loop_lce_L0 κ hκ6 N sqE hN hL

/-- **`log2_ceil_in_the_exponent__L15_L34`, placed and bounded.** -/
theorem log2_L15_completeAtB (κ : ℕ) (hκ6 : 6 ≤ κ) (N sqE : ℕ) (hN : N < 2 ^ 34)
    (hL : max 15 (log2Ceil N) < 34) :
    CompleteAtB fs cert κ "log2_ceil_in_the_exponent__L15_L34" (log2Lin sqE)
      [gen ^ N, ofK (Parameters.addressOfIndex sqE)] (Returns [gen ^ max 15 (log2Ceil N)])
      (fs "log2_ceil_in_the_exponent__L15_L34" + 34 + 2 * fs "assert_small_g_power") :=
  lce_completeAtB 15 (by norm_num) find_lce_L15 rfl core302_body loop_lce_L15 κ hκ6 N sqE hN hL

/-- **`log2_ceil_in_the_exponent__L0_L34`, placed.** -/
theorem log2_L0_completeAt (κ : ℕ) (hκ6 : 6 ≤ κ) : ∀ (N sqE : ℕ), N < 2 ^ 34 →
    max 0 (log2Ceil N) < 34 →
    CompleteAtD fs cert κ "log2_ceil_in_the_exponent__L0_L34" (log2Lin sqE)
      [gen ^ N, ofK (Parameters.addressOfIndex sqE)] (Returns [gen ^ max 0 (log2Ceil N)]) :=
  fun N sqE hN hL => (log2_L0_completeAtB κ hκ6 N sqE hN hL).toCompleteAtD

/-- **`log2_ceil_in_the_exponent__L15_L34`, placed.** -/
theorem log2_L15_completeAt (κ : ℕ) (hκ6 : 6 ≤ κ) : ∀ (N sqE : ℕ), N < 2 ^ 34 →
    max 15 (log2Ceil N) < 34 →
    CompleteAtD fs cert κ "log2_ceil_in_the_exponent__L15_L34" (log2Lin sqE)
      [gen ^ N, ofK (Parameters.addressOfIndex sqE)] (Returns [gen ^ max 15 (log2Ceil N)]) :=
  fun N sqE hN hL => (log2_L15_completeAtB κ hκ6 N sqE hN hL).toCompleteAtD

end
end LeanVM.Guest.B1
