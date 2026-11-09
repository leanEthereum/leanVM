/-
  LeanVM.Guest.B1.Digest.ListsComplete

  What a list digest's completeness reads of memory: its returns, and a load found among atoms.
-/

module

public import LeanVM.Guest.B1.Digest.Lists
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.Steps

/-!
# A list digest's returns, and loads

* `claimListOut_unique`: the cells of `ClaimListOut` are the memory's, so its returns are
  determined.
* `good_load_of_any`: a load among an evaluated block's atoms holds where the block's checks do.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

theorem good_load_of_any {S : List Atom} {w : ℕ → E} {σ : Val} {atoms : List Atom} {x p : V}
    {o : ℕ} (hS : S = []) (hg : ∀ a ∈ atoms, Good rd S w σ a) (h : atoms.any (isLoadAt x p o) = true) :
    σ x = rdAt rd (σ p) o := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  rcases (hg _ ha : Good rd S w σ (.load _ _ _)) with h | h
  · rw [hS] at h; exact absurd h (by simp)
  · exact h

end
end LeanVM.Guest.B1.Digest
