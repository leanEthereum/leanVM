/-
  LeanVM.Guest.B1.Placement.CompleteBase

  What the completeness proofs of `certify_placement` and `verify_tables` share: a memory defined
  below `2^k`, the word at a power of `g`.
-/

module

public import LeanVM.Guest.Core

/-!
# Memories defined below `2^k`

`LowDefB k rd`: the memory `rd` holds a word at every `g^i`, `i < 2^k`. `rdv rd a`: the word at
`g^a`, or `0`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The memory is defined below `2^k`. -/
def LowDefB (k : ℕ) (rd : Reader) : Prop := ∀ i < 2 ^ k, (rd (addressOfIndex i)).isSome

/-- The word at `g^a`, or `0`. -/
noncomputable def rdv (rd : Reader) (a : ℕ) : E := (rd (addressOfIndex a)).getD 0

theorem tb_ite_neg {c : Prop} [Decidable c] (h : ¬c) {α : Type} {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem tb_ite_pos {c : Prop} [Decidable c] (h : c) {α : Type} {a b : α} :
    (if c then a else b) = a := by simp [h]

end
end LeanVM.Guest.B1.Tables
