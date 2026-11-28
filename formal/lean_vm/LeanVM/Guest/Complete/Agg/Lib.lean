module

public import LeanVM.Guest.B1.Main.Aggregate
public import LeanVM.Guest.B1.Da.LevelsComplete
public import LeanVM.Guest.B1.Common.Basic

/-!
# Evaluated loads

On a valuation evaluated by `Fwd.ev`: a load that is not a store, reading a word in memory, has
its side condition (`side_load`) and its value is the memory's (`load_any_val`); a loop's
parameters are `.n 0 …` (`params_of_shape`).
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- A load (not a store) reading a word in memory has its side condition. -/
theorem side_load {d p : V} {o : ℕ} {v : E} (hS : Atom.load d p o ∉ S)
    (h : LoadHolds rd (σ p) o v) : Side rd S σ (.load d p o) := by
  simp only [Side]
  rw [LeanVM.Guest.B1.ite_neg' hS]
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- A load (not a store), evaluated, reads the memory. -/
theorem good_load_val {d p : V} {o : ℕ} (hS : Atom.load d p o ∉ S)
    (h : Good rd S w σ (.load d p o)) : σ d = rdAt rd (σ p) o := by
  rcases h with h | h
  · exact absurd h hS
  · exact h

/-- A load (not a store) found in an evaluated block reads the memory. -/
theorem load_any_val {atoms : List Atom} {x p : V} {o : ℕ} (hnS : ∀ a ∈ atoms, a ∉ S)
    (hg : ∀ a ∈ atoms, Good rd S w σ a) (h : atoms.any (isLoadAt x p o) = true) :
    σ x = rdAt rd (σ p) o ∧ Atom.load x p o ∈ atoms := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  exact ⟨good_load_val (hnS _ ha) (hg _ ha), ha⟩

theorem params_of_shape {fn : Fn} {f : String} {n : ℕ} (hs : loopShapeF fn f = true)
    (hl : fn.params.length = n) : fn.params = (List.range n).map V.n := by
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
  rw [hs.1.2, hl]

end
end LeanVM.Guest.Complete.Agg
