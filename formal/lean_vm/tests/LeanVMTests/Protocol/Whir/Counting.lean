/-
  LeanVMTests.Protocol.Whir.Counting

  The query, union, batching and quadratic-agreement counts on small instances over `ZMod 5`.
-/

import LeanVM.Protocol.ToArkLib.Whir.Counting
import Mathlib.Algebra.Field.ZMod

/-!
# Counting controls

* Two queries into `Fin 3` landing in a two-element set: `2² = 4` of the `9` query vectors.
* The discrepancy `(1, -1)` batches to `1 - λ`, zero at the single value `λ = 1 = J - 1`.
* `x²` and `1` agree at `x = ±1`: two points, attaining the bound `2`.

**Negative controls.** The zero discrepancy batches to zero at all `5` challenges, beyond
`J - 1 = 1`; equal coefficient vectors agree at all `5` points, beyond `2`. The nonvanishing and
distinctness hypotheses carry the bounds.
-/

namespace LeanVMTests.Protocol.Whir

open LeanVM.Protocol.Whir Finset

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

#guard (univ.filter fun x : Fin 2 → Fin 3 ↦ ∀ q, x q ∈ ({0, 1} : Finset (Fin 3))).card = 4

example : (univ.filter fun x : Fin 2 → Fin 3 ↦ ∀ q, x q ∈ ({0, 1} : Finset (Fin 3))).card =
    2 ^ 2 := by
  rw [card_forall_mem_fin]
  rfl

#guard (univ.filter fun l : ZMod 5 ↦
  ∑ t : Fin 2, (![1, -1] : Fin 2 → ZMod 5) t * l ^ t.val = 0).card = 1

example : (univ.filter fun l : ZMod 5 ↦
    ∑ t : Fin 2, (![1, -1] : Fin 2 → ZMod 5) t * l ^ t.val = 0).card ≤ 2 - 1 :=
  card_powerBatch_eq_zero_le _ ⟨0, by decide⟩

-- Negative control: the zero discrepancy vanishes at every challenge.
#guard (univ.filter fun l : ZMod 5 ↦
  ∑ t : Fin 2, (0 : Fin 2 → ZMod 5) t * l ^ t.val = 0).card = 5

#guard (univ.filter fun x : ZMod 5 ↦
  (![0, 0, 1] : Fin 3 → ZMod 5) 0 + x * ((![0, 0, 1] : Fin 3 → ZMod 5) 1 +
    x * (![0, 0, 1] : Fin 3 → ZMod 5) 2) =
  (![1, 0, 0] : Fin 3 → ZMod 5) 0 + x * ((![1, 0, 0] : Fin 3 → ZMod 5) 1 +
    x * (![1, 0, 0] : Fin 3 → ZMod 5) 2)).card = 2

example : (univ.filter fun x : ZMod 5 ↦
    (![0, 0, 1] : Fin 3 → ZMod 5) 0 + x * ((![0, 0, 1] : Fin 3 → ZMod 5) 1 +
      x * (![0, 0, 1] : Fin 3 → ZMod 5) 2) =
    (![1, 0, 0] : Fin 3 → ZMod 5) 0 + x * ((![1, 0, 0] : Fin 3 → ZMod 5) 1 +
      x * (![1, 0, 0] : Fin 3 → ZMod 5) 2)).card ≤ 2 :=
  card_quadratic_eq_le _ _ (by decide)

-- Negative control: equal quadratics agree everywhere.
#guard (univ.filter fun x : ZMod 5 ↦
  (![0, 0, 1] : Fin 3 → ZMod 5) 0 + x * ((![0, 0, 1] : Fin 3 → ZMod 5) 1 +
    x * (![0, 0, 1] : Fin 3 → ZMod 5) 2) =
  (![0, 0, 1] : Fin 3 → ZMod 5) 0 + x * ((![0, 0, 1] : Fin 3 → ZMod 5) 1 +
    x * (![0, 0, 1] : Fin 3 → ZMod 5) 2)).card = 5

/-- The union bound over a two-member list, each member with at most one bad challenge. -/
example (bad : Fin 2 → ZMod 5 → Prop) [∀ U, DecidablePred (bad U)]
    [DecidablePred fun s ↦ ∃ U ∈ (univ : Finset (Fin 2)), bad U s]
    (h : ∀ U ∈ (univ : Finset (Fin 2)), (univ.filter (bad U)).card ≤ 1) :
    (univ.filter fun s ↦ ∃ U ∈ (univ : Finset (Fin 2)), bad U s).card ≤ 2 := by
  simpa using card_filter_exists_le univ bad h

end LeanVMTests.Protocol.Whir
