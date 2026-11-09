/-
  LeanVM.Guest.B1.KeccakGkr.StoreFacts

  Kernel-checkable facts about a block's stores, and `keccak_layer`'s position rounds.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LocalRounds

/-!
# Stores

`noStoreVia ps S`: no store of `S` goes through a pointer of `ps` (`not_mem_of_noStoreVia`).
`noneIn as S`: none of the atoms `as` is a store of `S` (`not_mem_of_noneIn`). `localS`:
`keccak_layer`'s position rounds (`localRoundsT` from the cursor `1078`, the local point `1081`,
the value `1079` and the capacity `1073 ..`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1

@[expose] public section

/-- The position rounds. -/
def localS : List Stmt := localRoundsT (.n 1078) (.n 1081) (.n 1079) (cap5 1073) 1082 11

/-- No store goes through the pointers `ps`. -/
def noStoreVia (ps : List V) (S : List Atom) : Bool := S.all fun a ↦ match a with
  | .load _ p _ => !ps.contains p
  | _ => true

theorem not_mem_of_noStoreVia {ps : List V} {S : List Atom} (h : noStoreVia ps S = true) {p : V}
    (hp : p ∈ ps) (d : V) (off : ℕ) : Atom.load d p off ∉ S := by
  intro hm
  have h' := List.all_eq_true.mp h _ hm
  simp only at h'
  rw [List.contains_iff_mem.mpr hp] at h'
  exact absurd h' (by decide)

/-- None of the atoms `as` is a store. -/
def noneIn (as S : List Atom) : Bool := as.all fun a ↦ !S.contains a

theorem not_mem_of_noneIn {as S : List Atom} (h : noneIn as S = true) : ∀ a ∈ as, a ∉ S := by
  intro a ha hm
  have h' := List.all_eq_true.mp h a ha
  rw [List.contains_iff_mem.mpr hm] at h'
  exact absurd h' (by decide)

end
end LeanVM.Guest.B1.VerifySub
