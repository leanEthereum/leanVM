/-
  LeanVM.Guest.B1.Tables.VtC.AComplete

  `verify_tables`' buffers placed: the caller's buffers and its own from an offset.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ARelIn
public import LeanVM.Guest.B1.Tables.VtC.Lift

/-!
# `verify_tables`, placed

`VtBases.at B o`: the caller's buffers of `B`, the own buffers from `o`. `forall₂_length_le`: words
fit buffers of their lengths.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The caller's buffers of `B`, the own buffers from `o`. -/
def VtBases.at (B : VtBases) (o : ℕ) : VtBases := { B with own := o }

theorem forall₂_length_le : ∀ l : List (List E),
    List.Forall₂ (fun c s => c.length ≤ s) l (l.map List.length)
  | [] => .nil
  | _ :: l => .cons le_rfl (forall₂_length_le l)

end
end LeanVM.Guest.B1.Tables
