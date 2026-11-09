/-
  LeanVM.Guest.B1.Tables.VtC.AComplete

  **`verify_tables` is complete, placed**: on the caller's honest buffers, from the
  specification's accepting run.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ARelIn
public import LeanVM.Guest.B1.Tables.VtC.Lift

/-!
# `verify_tables`, placed

`VtBases.at B o`: the caller's buffers of `B`, the own buffers from `o`. `verify_tables_completeAt`:
`vt_completeAt` on the caller's honest buffers `H.linL B`, the own buffers' honest words
`H.ownW B` at the allocator's positions from `fp + fs "verify_tables"`, the oracle `vtW`, the
returns `H.retsH B`; its run from `vt_rel_complete_vtW` and `vt_relIn_complete` on every memory
defined below `2^κ`, `κ ≥ 14` (the rank keys' range check against `g^8635`), holding that
layout.
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

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_tables` is complete, placed**: from the specification's accepting run (`H.Ok`) and
the deployed shapes (`VtShape`), on the caller's honest buffers `H.linL B`, with the arguments
`H.args B`, returning `H.retsH B`, for memories defined below `2^κ`, `κ ≥ 14`. -/
theorem verify_tables_completeAt {κ : ℕ} (hκ : 14 ≤ κ) {H : VtHonest} (h : H.Ok)
    (hs : VtShape H) (B : VtBases) :
    CompleteAtD fs cert κ "verify_tables" (H.linL B) (H.args B) (Returns (H.retsH B)) := by
  refine vt_completeAt (H.linL B) (H.args B) (H.retsH B) rfl H.sizes (fun _ ↦ H.ownW B)
    (fun _ ↦ by rw [← ownW_lengths H B]; exact forall₂_length_le _)
    (fun fp ↦ vtW H (B.at (fp + fs "verify_tables")))
    (fun fp ↦ H.bufs (B.at (fp + fs "verify_tables"))) ?_ ?_
  · intro fp q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    refine ⟨q'.1, rfl, fun i hi ↦ ?_⟩
    unfold RegionL
    exact ⟨q', hq', by omega, by omega⟩
  · intro fp rd hlow hL
    have hlow14 : LowDefB 14 rd := hlow.mono hκ
    have hm : MemLay rd (H.linL (B.at (fp + fs "verify_tables")) ++
        H.ownL (B.at (fp + fs "verify_tables"))) := hL
    obtain ⟨-, h2, h3, h4, h5⟩ :=
      vt_rel_complete_vtW h hs (B.at (fp + fs "verify_tables")) hlow14 hm
    exact ⟨vt_relIn_complete h hs _ (vtW_ok H _) hlow14 hm, h2, h3, h4, h5⟩

end
end LeanVM.Guest.B1.Tables
