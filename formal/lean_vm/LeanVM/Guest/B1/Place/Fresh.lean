/-
  LeanVM.Guest.B1.Place.Fresh

  A memory defined everywhere that holds a layout of disjoint runs below the order of `g`.
-/

module

public import LeanVM.Guest.B1.Selectors.LayoutBasic
public import LeanVM.Guest.Memory.Uniform

/-!
# A fresh memory

`freshRd L`: `layRd L` (a run's word at its addresses) with `0` elsewhere, so defined below every
`2^κ` (`lowDef_freshRd`); it holds `L` when its runs are disjoint and below the order of `g`
(`memL_freshRd`). `fresh_exists`: such a memory exists.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The layout's words at its addresses, `0` elsewhere. -/
noncomputable def freshRd (L : Layout) : Reader := fun a ↦ some ((Tables.layRd L a).getD 0)

theorem lowDef_freshRd (κ : ℕ) (L : Layout) : LowDef κ (freshRd L) := fun _ _ ↦ rfl

theorem memL_freshRd {L : Layout} (hd : DisjL L) (hl : ∀ q ∈ L, q.1 + q.2.length < 2 ^ 64 - 1) :
    MemL (freshRd L) L := by
  intro q hq j hj
  have h := Tables.memLay_layRd (L := L) hd hl q hq j hj
  refine ⟨h.1, ?_⟩
  show some ((Tables.layRd L _).getD 0) = _
  rw [h.2]
  rfl

/-- **A memory defined low holds a layout of disjoint runs below the order of `g`.** -/
theorem fresh_exists (κ : ℕ) {L : Layout} (hd : DisjL L)
    (hl : ∀ q ∈ L, q.1 + q.2.length < 2 ^ 64 - 1) : ∃ rd, LowDef κ rd ∧ MemL rd L :=
  ⟨freshRd L, lowDef_freshRd κ L, memL_freshRd hd hl⟩

end
end LeanVM.Guest.B1
