/-
  LeanVM.Guest.B1.Place.Fresh

  A memory defined everywhere that holds a layout of disjoint runs below the order of `g`.
-/

module

public import LeanVM.Guest.B1.Selectors.LayoutBasic
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Memory.Size

/-!
# A fresh memory

`freshRd L`: `layRd L` (a run's word at its addresses) with `0` elsewhere, so defined below every
`2^κ` (`lowDef_freshRd`); it holds `L` when its runs are disjoint and below the order of `g`
(`memL_freshRd`). `fresh_exists`: such a memory exists; `fresh_pair`: one holding a layout below
`b` and one within `[b, b + n)`. `relAtIn_le`: a words bound of a function's trees bounds a placed
tree's words.
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

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A words bound of a function's trees bounds a placed tree's words.** -/
theorem relAtIn_le {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtIn coreProgram fs cert rd R D fp n f args rets) {B : ℕ}
    (hT : TotalLe coreProgram fs f (fun _ ↦ B)) : n ≤ B := by
  obtain ⟨t, hn, hv, hb, -, ht, -⟩ := h
  rw [← ht]
  exact hT rd t args rets hn hv hb

theorem relAtIn_leOn {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtIn coreProgram fs cert rd R D fp n f args rets) {Pre : List E → Prop} {B : ℕ}
    (hT : TotalLeOn coreProgram fs f Pre (fun _ ↦ B)) (hp : Pre args) : n ≤ B := by
  obtain ⟨t, hn, hv, hb, -, ht, -⟩ := h
  rw [← ht]
  exact hT rd t args rets hn hp hv hb

/-- Two layouts, one below `b` and one within `[b, b + n)`, disjoint and below the order of `g`. -/
theorem fresh_pair (κ : ℕ) {L Lin : Layout} {b n : ℕ} (hd : DisjL L) (hw : Within L b n)
    (hd' : DisjL Lin) (hw' : Within Lin 0 b) (hlt : b + n < 2 ^ 64 - 1) :
    ∃ rd, LowDef κ rd ∧ MemL rd (L ++ Lin) := by
  refine fresh_exists κ ?_ fun q hq ↦ ?_
  · refine List.pairwise_append.mpr ⟨hd, hd', fun a ha c hc ↦ Or.inr ?_⟩
    have := hw a ha
    have := hw' c hc
    omega
  · rcases List.mem_append.mp hq with hq | hq
    · have := hw q hq; omega
    · have := hw' q hq; omega

end
end LeanVM.Guest.B1
