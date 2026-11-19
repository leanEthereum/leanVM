module

public import NativeVm.Code.Contracts

/-!
# Phase 2's model step, unfolded

Within the window phase 1 checks (`16 ≤ stackLog ≤ 30`, `1 ≤ rate ≤ 4`) the ladder exists and its
level `0` folds `initialFold` variables at the rate exponent `rate` (`ladder_head`, checked over the
window by `decide +kernel`), so `commitStack` reads the root of `2^(stackLog − 6 + rate)` leaves of
`64` words, and `phase2M` is that read, the grind, the `stackLog` challenges and the value
(`phase2M_eq`).
-/

@[expose] public section

namespace NativeVm.Code

open NativeVm.Model LeanVM.Parameters

/-- The ladder's geometry has a query count per level over the window. -/
theorem ladder_lengths : ∀ a < 15, ∀ b < 4, (Whir.ladderShape (a + 16) (b + 1)).length =
    ((Whir.queryTable.getD b []).getD a []).length := by
  decide +kernel

/-- **The ladder's level `0`** over the window: `initialFold` variables at the rate exponent. -/
theorem ladder_head {μ r : Nat} (h1 : 16 ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    ∃ q rest, Whir.ladder μ r = some (⟨Whir.initialFold, r, q⟩ :: rest) := by
  obtain ⟨a, rfl⟩ : ∃ a, μ = a + 16 := ⟨μ - 16, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  have hl := ladder_lengths a (by omega) b (by omega)
  have hadm : Whir.Admissible (a + 16) (b + 1) := ⟨h1, h2, h3, h4⟩
  simp only [Whir.ladder, hadm, ↓reduceIte, Whir.minLogStack, Nat.add_sub_cancel, hl]
  generalize (Whir.queryTable.getD b []).getD a [] = qs at hl ⊢
  cases qs with
  | nil => simp [Whir.ladderShape] at hl
  | cons q rest => exact ⟨q, _, rfl⟩

/-- **`phase2M` unfolded** over the window. -/
theorem phase2M_eq {layout : LayoutW} {rate : Nat} (h1 : 16 ≤ layout.stackLog)
    (h2 : layout.stackLog ≤ 30) (h3 : 1 ≤ rate) (h4 : rate ≤ 4) :
    phase2M layout rate = (readCommitment (layout.stackLog - 6 + rate) 64 >>= fun _ ↦
      grind 15 >>= fun _ ↦ sampleChallenges layout.stackLog >>= fun z ↦
        readScalar >>= fun v ↦ pure (⟨.eq z, v⟩ : StackClaimW)) := by
  obtain ⟨q, rest, hl⟩ := ladder_head h1 h2 h3 h4
  unfold phase2M commitStack readOod
  rw [hl]
  rfl

end NativeVm.Code
