module

public import LeanVM.Cost.Bounds.FastPath

/-!
# Bounds: generic library prices

`listFoldl_le_sum` (a closure's price depending on the element), `bind_cost`, `finRangeFrom_cost`
(the others: `Bounds/ListLib.lean`, `Bounds/FieldLib.lean`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

/-- `List.foldl`, the closure's price depending on the element. -/
theorem listFoldl_le_sum {α β : Type} [MachineEncoding α] [MachineEncoding β] (hP : Includes P listFoldl.costDeps)
    (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (B : β → ℕ) :
    ∀ (l : List β) (init : α), (∀ acc : α, ∀ b ∈ l, appCost P fVal [encodeValue acc, encodeValue b] ≤ B b) →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤ (l.map fun b ↦ B b + 11).sum + 3 := by
  intro l
  induction l with
  | nil => intro init _; rw [listFoldl.costEq_nil P hP f fVal hf]; simp
  | cons b l ih =>
    intro init hB
    rw [listFoldl.costEq_cons P hP f fVal hf]
    have h1 := ih (f init b) (fun acc b' hb ↦ hB acc b' (by simp [hb]))
    have h2 := hB init b (by simp)
    simp only [List.map_cons, List.sum_cons]
    omega

section Generic
variable {α β : Type} [MachineEncoding α] [MachineEncoding β]

/-- `Option.bind` (`bind.c47`): the closure's price on the value bound, `+ 6`. -/
theorem bind_le (hP : Includes P Auto.Option.bind.c47.costDeps) (f : α → Option β) (fVal : MachineValue)
    (hf : ∀ a, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (o : Option α) (B : ℕ)
    (hB : ∀ a, o = some a → appCost P fVal [encodeValue a] ≤ B) :
    machineCost P Auto.Option.bind.c47.costIdx [encodeValue o, fVal] ≤ B + 6 := by
  cases o with
  | none => rw [Auto.Option.bind.c47.costEq_none P hP f fVal hf]; omega
  | some a => rw [Auto.Option.bind.c47.costEq_some P hP a f fVal hf]; have := hB a rfl; omega

/-- `Option.bind` (`bind.c47`): the closure's price and `6` at most. -/
theorem bind_cost (hP : Includes P Auto.Option.bind.c47.costDeps) (f : α → Option β) (fVal : MachineValue)
    (hf : ∀ a : α, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ) (hB : ∀ a : α, appCost P fVal [encodeValue a] ≤ B)
    (o : Option α) : machineCost P Auto.Option.bind.c47.costIdx [encodeValue o, fVal] ≤ B + 6 :=
  bind_le P hP f fVal hf o B fun a _ ↦ hB a

/-- `List.finRange` from `i` (`finRangeFrom.c170`): `13` per element, `5` at the end. -/
theorem finRangeFrom_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.finRangeFrom.c104.costDeps)
    (n : ℕ) (hn : n < 2 ^ 64) : ∀ i, i ≤ n →
      machineCost P Auto.LeanVM.Cost.Rewrite.finRangeFrom.c104.costIdx [encodeValue n, encodeValue i] ≤
        13 * (n - i) + 5 := by
  intro i hi
  induction hk : n - i generalizing i with
  | zero =>
    rw [Auto.LeanVM.Cost.Rewrite.finRangeFrom.c104.costEq P hP, limbs_of_lt (by omega : i < 2 ^ 64),
      limbs_of_lt hn]
    simp only [show ¬i < n by omega, ↓reduceDIte]
    omega
  | succ k ih =>
    rw [Auto.LeanVM.Cost.Rewrite.finRangeFrom.c104.costEq P hP, limbs_of_lt (by omega : i < 2 ^ 64),
      limbs_of_lt hn]
    simp only [show i < n by omega, ↓reduceDIte]
    have := ih (i + 1) (by omega) (by omega)
    rw [limbs_of_lt (by omega : i + 1 < 2 ^ 64)]
    omega

end Generic

end

end LeanVM.Cost.Bounds
