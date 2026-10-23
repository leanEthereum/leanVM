/-
  LeanVM.Guest.Memory.GuestWords

  The guest's static certificates counting words at the frame sizes, checked but for the functions
  left to hand bounds (`coreProgram_wchecked`), and the words bounds they give (`core_total_le_of_stat`,
  `core_total_le_of_loop`, `core_totalLe`).
-/

module

public import LeanVM.Guest.Memory.GuestWords.All
public import LeanVM.Guest.Memory.GuestStatic
public import LeanVM.Guest.Memory.StaticWords
public import LeanVM.Guest.Frames

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics Core Memory Data

@[expose] public section

/-- The frame sizes, by core index. -/
def wfsList : List ℕ := Data.frameSizes.drop 1

/-- The frame size of function `j`. -/
def wfsJ (j : ℕ) : ℕ := wfsList.getD j 0

/-- The certificates counting words were made at the frame sizes. -/
theorem womegaJ_list : (List.range coreProgram.length).map womegaJ = wfsList := by
  rw [coreProgram_length]; decide +kernel

theorem womegaJ_eq' {j : ℕ} (hj : j < coreProgram.length) : womegaJ j = wfsJ j := by
  rw [wfsJ, ← womegaJ_list, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- The hand list names its functions. -/
theorem whandJ_names : whandJ.all (fun q => decide ((coreProgram[q.1]?).map Fn.name = some q.2)) = true := by
  decide +kernel

/-- The functions left to hand bounds. -/
def wHandX (g : String) : Prop := ∃ q ∈ whandJ, q.2 = g

/-- The guest's certificates counting words, by name. -/
noncomputable def wcertOf (g : String) : Cert := wcertJ (coreIdx g)

theorem wcertOf_of_idx {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) :
    wcertOf g = wcertJ j := by
  rw [wcertOf, coreIdx_of_name h]

theorem wfs_of_idx {fs : String → ℕ} (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j)
    {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) : fs g = womegaJ j := by
  rcases hj : coreProgram[j]? with _ | fn
  · rw [hj] at h; exact absurd h (by simp)
  · rw [hj] at h
    obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h, ← hfn, hF j hlt, womegaJ_eq' hlt]

theorem wlookJ_ok {j : ℕ}
    (hl : (wlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true) :
    LookOk (wlookJ j) wcertOf := by
  intro g hg
  unfold wlookJ at hg ⊢
  rcases hf : (wlnkJ j).find (nameKey g) with _ | q
  · rw [hf] at hg; exact absurd rfl hg
  · rw [hf] at hg
    dsimp only at hg ⊢
    by_cases hq : g = q.1
    · have hp := NTree.find_all hl hf
      simp only [decide_eq_true_eq] at hp
      rw [ite_eq_left (c := g = q.1) hq, wcertOf_of_idx (hq ▸ hp)]
    · rw [ite_eq_right (c := g = q.1) hq] at hg; exact absurd rfl hg

theorem womLookJ_ok {fs : String → ℕ} (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j)
    {j : ℕ} (hl : (wlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true) :
    WlOk (womLookJ j) fs := by
  intro g n hg
  unfold womLookJ at hg
  rcases hf : (wlnkJ j).find (nameKey g) with _ | q
  · rw [hf] at hg; cases hg
  · rw [hf] at hg
    dsimp only at hg
    by_cases hq : g = q.1
    · rw [ite_eq_left (c := g = q.1) hq, Option.some.injEq] at hg
      have hp := NTree.find_all hl hf
      simp only [decide_eq_true_eq] at hp
      rw [wfs_of_idx hF (hq ▸ hp), hg]
    · rw [ite_eq_right (c := g = q.1) hq] at hg; cases hg

/-- **The guest's certificates counting words check at the frame sizes**, but for the functions
left to hand bounds. -/
theorem coreProgram_wchecked {fs : String → ℕ}
    (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j) :
    CheckedExcept coreProgram true wcertOf fs wHandX := by
  intro fn hfn hX
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfn
  have hc := wchkIdx_all j (by rw [coreProgram_length] at hj; exact hj)
  unfold wchkIdx at hc
  rw [List.getElem?_eq_getElem hj] at hc
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
  rcases hc with hh | hc
  · exfalso
    obtain ⟨q, hq, hqj⟩ := List.any_eq_true.mp hh
    simp only [beq_iff_eq] at hqj
    have hn := List.all_eq_true.mp whandJ_names q hq
    simp only [decide_eq_true_eq, hqj, List.getElem?_eq_getElem hj, Option.map_some,
      Option.some.injEq] at hn
    exact hX ⟨q, hq, hn.symm⟩
  · refine ⟨wlookJ j, womLookJ j, wlookJ_ok hc.1, womLookJ_ok hF hc.1, ?_⟩
    rw [wcertOf, coreIdx_getElem hj, wfs_of_idx hF (j := j) (by simp [List.getElem?_eq_getElem hj])]
    exact hc.2

/-- `HandOk` function by function: each hand bound by `bound_of_total`, its certificate read by
`wcertOf_of_idx`. -/
theorem handOk_of {fs : String → ℕ}
    (h : ∀ q ∈ whandJ, ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = q.2 →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → Bound coreProgram true wcertOf fs t args) :
    HandOk coreProgram fs wcertOf wHandX := by
  rintro f ⟨q, hq, rfl⟩
  exact h q hq

/-- **A guest function's words**, by its certificate counting words. -/
theorem core_total_le_of_stat {fs : String → ℕ}
    (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j)
    (hX : HandOk coreProgram fs wcertOf wHandX) {f : String}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : wcertOf f = .stat pre b ks)
    {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) (hpre : ArgsPre pre args) :
    t.total fs ≤ b.eval args :=
  total_le_of_stat (coreProgram_wchecked hF) hX hcf hn hv hb hpre

/-- **A guest loop's words**, by its certificate counting words. -/
theorem core_total_le_of_loop {fs : String → ℕ}
    (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j)
    (hX : HandOk coreProgram fs wcertOf wHandX) {f : String} {endc : Option ℕ}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : wcertOf f = .loop endc pre b ks)
    {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) {a e : ℕ}
    (ha : args.getD 0 0 = ofK (gpow a)) (he : endOf endc args = ofK (gpow e)) (hae : a < e)
    (heo : e < 2 ^ 64 - 1) (hpre : ArgsPre pre args) : t.total fs ≤ (e - a) * b.eval args :=
  total_le_of_loop (coreProgram_wchecked hF) hX hcf hn hv hb ha he hae heo hpre

/-- **A guest function's words, constant.** -/
theorem core_totalLe {fs : String → ℕ}
    (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j)
    (hX : HandOk coreProgram fs wcertOf wHandX) {f : String} {B : ℕ}
    {ks : List (V × ℕ)} (hcf : wcertOf f = .stat [] ⟨B, []⟩ ks) : TotalLe coreProgram fs f fun _ => B :=
  totalLe_of_stat (coreProgram_wchecked hF) hX hcf

end
end LeanVM.Guest
