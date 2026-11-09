module

public import LeanVM.Cost.Bounds.Decoder.Lane
public import LeanVM.Cost.Bounds.Sizes.Pruning
public import LeanVM.Cost.Extractor.Runner

/-!
# Bound: a fold over a range, its closure's price bounded on the states it reaches

`listFoldl_range'_le`, which the pruning of the lanes against the word (`pruneUpToPMC_cost`,
`Bounds/PMLane/Decode.lean`, `≤ pruneBound …`) folds by.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-- **`List.foldl` over `List.range' s n`, the closure's price bounded on the states the fold
reaches**: `11` per element and the closure's price, `3`. -/
theorem listFoldl_range'_le (hP : Includes P listFoldl.costDeps) {α : Type} [MachineEncoding α]
    (f : α → ℕ → α) (fVal : MachineValue) (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b)))
    (B : ℕ) :
    ∀ (n s : ℕ) (st : α),
      (∀ j, s ≤ j → j < s + n →
        appCost P fVal [encodeValue ((List.range' s (j - s)).foldl f st), encodeValue j] ≤ B) →
      machineCost P listFoldl.costIdx [fVal, encodeValue st, encodeValue (List.range' s n)] ≤ (B + 11) * n + 3 := by
  intro n
  induction n with
  | zero => intro s st _; rw [List.range'_zero, listFoldl.costEq_nil P hP f fVal hf]; omega
  | succ n ih =>
    intro s st hB
    rw [List.range'_succ, listFoldl.costEq_cons P hP f fVal hf]
    have h1 := hB s le_rfl (by omega)
    simp only [Nat.sub_self, List.range'_zero, List.foldl_nil] at h1
    have h2 := ih (s + 1) (f st s) (fun j hj1 hj2 ↦ by
      have := hB j (by omega) (by omega)
      have e : j - s = (j - (s + 1)) + 1 := by omega
      rw [e, List.range'_succ, List.foldl_cons] at this
      exact this)
    have e : (B + 11) * (n + 1) = (B + 11) * n + B + 11 := by ring
    omega

end

end LeanVM.Cost.Bounds.Decoder
