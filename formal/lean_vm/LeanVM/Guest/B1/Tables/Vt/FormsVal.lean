/-
  LeanVM.Guest.B1.Tables.Vt.FormsVal

  The values `verify_tables` computes from the baked coordinate terms: a coordinate's at a table's
  evaluations, a block's on a side, a table's form on a side.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsData

/-!
# The forms' values (G:2647-2674)

For a table's evaluations `ev`, a side's challenge `β` and slot weights `W`, the guest computes
each block's `β + Σ_slot W_slot · coordinate_slot(ev)` from the baked terms (`vtBlockVal`), and
the table's form on the side as the blocks' selectors times their values (`vtSideVal`); on the
count side `β = 0` and `W = 1`. `vtBlockVal_eq` unfolds a block's value slot by slot.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsEval termsEval_cons termsEval_nil)

@[expose] public section

/-- A coordinate's value at the evaluations `ev`: its baked terms' value. -/
def vtCoordVal (ev : ℕ → E) (c : List (List ℕ × ℕ)) : E := termsEval ev (liftT (vtTermsK c))

/-- A block's value on a side: `β + Σ_slot W_slot · coordinate_slot`. -/
def vtBlockVal (β : E) (W ev : ℕ → E) (blk : List (List (List ℕ × ℕ))) : E :=
  β + (blk.zipIdx.map fun cs ↦ W cs.2 * vtCoordVal ev cs.1).sum

/-- A table's form on a side: its blocks' selectors times their values. -/
def vtSideVal (sels : List E) (β : E) (W ev : ℕ → E)
    (blks : List (List (List (List ℕ × ℕ)))) : E :=
  (List.zipWith (fun s blk ↦ s * vtBlockVal β W ev blk) sels blks).sum

/-- The slots from `i` on. -/
def vtSlots (W ev : ℕ → E) : ℕ → List (List (List ℕ × ℕ)) → E
  | _, [] => 0
  | i, c :: cs => W i * vtCoordVal ev c + vtSlots W ev (i + 1) cs

theorem vtSlots_eq (W ev : ℕ → E) :
    ∀ (blk : List (List (List ℕ × ℕ))) (i : ℕ),
      ((blk.zipIdx i).map fun cs ↦ W cs.2 * vtCoordVal ev cs.1).sum = vtSlots W ev i blk
  | [], _ => rfl
  | c :: cs, i => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, vtSlots_eq W ev cs (i + 1)]
    rfl

theorem vtBlockVal_eq (β : E) (W ev : ℕ → E) (blk : List (List (List ℕ × ℕ))) :
    vtBlockVal β W ev blk = β + vtSlots W ev 0 blk := by
  rw [vtBlockVal, vtSlots_eq]

theorem vtCoordVal_nil (ev : ℕ → E) : vtCoordVal ev [] = 0 := rfl

theorem vtCoordVal_cons (ev : ℕ → E) (m : List ℕ) (c : ℕ) (l : List (List ℕ × ℕ)) :
    vtCoordVal ev ((m, c) :: l) = ofK (K.ofBits c) * (m.map ev).prod + vtCoordVal ev l := by
  simp [vtCoordVal, vtTermsK, liftT]

theorem vt_word_ofK (n : ℕ) : word n 0 = ofK (K.ofBits n) := by rw [tb_word_eOfNat]; rfl

theorem vt_ofK_ofBits_zero : ofK (K.ofBits 0) = 0 := by rw [← vt_word_ofK, tb_word_zero]

theorem vt_ofK_ofBits_one : ofK (K.ofBits 1) = 1 := by rw [← vt_word_ofK, tb_word_one]

end
end LeanVM.Guest.B1.Tables
