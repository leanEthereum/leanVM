/-
  LeanVM.Guest.B1.Main.AggCLib

  What an evaluated valuation (`Fwd.ev`) gives of `fs_pack`s and loads, for the
  completeness of `aggregate_claims` and its loops.
-/

module

public import LeanVM.Guest.B1.Main.AggCDefs
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Digest.LoopComplete

/-!
# Evaluated templates

`pack_vals`: an `fs_pack(x)` from `b` whose atoms are in a block, evaluated, has the honest values
`fsPackVals (σ x) 1`, so its cells are the scalar's rate cells (`pack_cells`). `side_load`: a
load (not a store) reading a word in memory has its side condition; `good_load_val`: its value is
the memory's.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd

@[expose] public section

-- `Fwd`'s `Side`/`Good` decide membership with the core `DecidableEq Atom`; `Sig.Decide`'s (reaching
-- here through `Sig.Interface`) would elaborate the `if`s below differently
attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem good_of_any {A : List Atom} (hg : ∀ a ∈ A, Good rd S w σ a) {a : Atom}
    (h : A.any (atomEqb a) = true) : Good rd S w σ a := by
  obtain ⟨a', ha', he⟩ := List.any_eq_true.mp h
  rw [atomEqb_sound he]
  exact hg a' ha'

/-- **An evaluated `fs_pack`** has its honest values. -/
theorem pack_vals {A : List Atom} {x : V} {b : ℕ} (h : packIn A x b = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) : ∀ i < 2, σ (.n (b + i)) = fsPackVals (σ x) dsObserve i := by
  have hall := List.all_eq_true.mp h
  have g0 : σ (.n b) = σ x := good_of_any hg (hall (.copy (.n b) x) (by simp [fsPackA]))
  have g1 : σ (.n (b + 1)) = word 0 dsObserve :=
    good_of_any hg (hall (.const (.n (b + 1)) (word 0 dsObserve)) (by simp [fsPackA]))
  intro i hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · exact g0
  · exact g1

theorem pack_ok {A : List Atom} {x : V} {b : ℕ} (h : packIn A x b = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) : FsPackOk σ x b dsObserve :=
  fsPackOk_of_vals (pack_vals h hg)

/-- An evaluated `fs_pack`'s cells are its scalar's rate cells. -/
theorem pack_cells {A : List Atom} {x : V} {b : ℕ} (h : packIn A x b = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) :
    (σ (.n b), σ (.n (b + 1))) = Keccak.scalarCells (σ x) dsObserve :=
  fsPackT_cells (pack_ok h hg)

/-- A load (not a store) reading a word in memory has its side condition. -/
theorem side_load {d p : V} {o : ℕ} {v : E} (hS : Atom.load d p o ∉ S)
    (h : LoadHolds rd (σ p) o v) : Side rd S σ (.load d p o) := by
  simp only [Side]
  rw [ite_neg' hS]
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- A load (not a store), evaluated, reads the memory. -/
theorem good_load_val {d p : V} {o : ℕ} (hS : Atom.load d p o ∉ S)
    (h : Good rd S w σ (.load d p o)) : σ d = rdAt rd (σ p) o := by
  rcases h with h | h
  · exact absurd h hS
  · exact h

/-- A load (not a store) of a word in memory, evaluated, holds and reads it. -/
theorem load_of_good {d p : V} {o : ℕ} {v : E} (hS : Atom.load d p o ∉ S)
    (hg : Good rd S w σ (.load d p o)) (h : LoadHolds rd (σ p) o v) :
    σ d = v ∧ (Atom.load d p o).Holds rd σ := by
  have e : σ d = v := by rw [good_load_val hS hg, rdAt_of_load h]
  refine ⟨e, ?_⟩
  show LoadHolds rd (σ p) o (σ d)
  rw [e]; exact h

/-- A load (not a store) found in an evaluated block reads the memory. -/
theorem load_any_val {atoms : List Atom} {x p : V} {o : ℕ} (hnS : ∀ a ∈ atoms, a ∉ S)
    (hg : ∀ a ∈ atoms, Good rd S w σ a) (h : atoms.any (isLoadAt x p o) = true) :
    σ x = rdAt rd (σ p) o ∧ Atom.load x p o ∈ atoms := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  exact ⟨good_load_val (hnS _ ha) (hg _ ha), ha⟩

end
end LeanVM.Guest.B1.Main
