/-
  LeanVM.Guest.B1.VerifySub.H.TermCtx

  What `check_opening_terminal` takes of an honest child's claims: `verify_tables`' context
  (`TCtx`) on the honest memory, and the WHIR terminal point's length.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Sec

/-!
# The terminal's context

`ptsP H j`: honest claim `j`'s point (the bus point cut to `logMemory` four times, to `19` once,
`chi` cut to evaluation `j - 5`'s table's height, the public input's point); `vtH_ptsP`: the
honest claims' points are those. `vtH_tctx`: on a memory holding the bus point at `zeta`, `chi`'s
words, `TCtx` holds of the honest layout, bus result and claims (each pooled claim's point has the
low dimension `claimLowDim` the terminal derives from `kappa_base`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace VtHonest

/-- Honest claim `j`'s point. -/
noncomputable def ptsP (H : VtHonest) (j : ℕ) : List E :=
  if j < 4 then H.point.take H.lm else if j = 4 then H.point.take 19
  else if j < 164 then H.chiW.take (vtHt H.rows (vsEvTab (j - 5)))
  else H.rm :: List.replicate ((H.L.placement memory0).variableCount - 1) 0

variable {H : VtHonest}

theorem vtH_ptsP (h : H.Ok) (hr : H.rows.length = 6) (hbc : H.bc.length = 2 ^ 23) :
    H.claims.map (·.point) = (List.range 167).map H.ptsP := by
  rw [vtH_points h hr hbc]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_map, List.getElem_range, ptsP]
  have e4 : (List.replicate 4 (H.point.take H.lm) ++ [H.point.take 19]).length = 5 := by simp
  have e157 : ((List.range 159).map fun k ↦ H.chiW.take (vtHt H.rows (vsEvTab k))).length = 159 := by
    simp
  by_cases hj4 : j < 4
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simp; omega)]
    simp only [hj4, ↓reduceIte]
    interval_cases j <;> rfl
  by_cases hj5 : j = 4
  · subst hj5
    rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp)]
    simp
  by_cases hj162 : j < 164
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil,
      List.getElem_map, List.getElem_range, hj4, hj5, hj162, ↓reduceIte]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_replicate, hj4, hj5, hj162, ↓reduceIte]

theorem take_self_len (l : List E) (k : ℕ) : l.take k = l.take (l.take k).length := by
  rw [List.length_take]; exact List.take_eq_take_min

theorem chiW_length (H : VtHonest) : H.chiW.length = H.n := by
  simp [VtHonest.chiW, zcChis]

theorem vsEvTab_lt : ∀ k < 159, vsEvTab k < 6 := by decide +kernel

theorem vtH_n_ge (hr : H.rows.length = 6) {t : ℕ} (ht : t < 6) : vtHt H.rows t ≤ H.n :=
  VerifySub.mem_le_foldl_max 0 (by
    rw [vt_tableHeights_eq hr]; exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)

theorem vsFoldl_max_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => Or.inl rfl
  | y :: l, a => by
    rcases vsFoldl_max_mem l (max a y) with h | h
    · simp only [List.foldl_cons, h]
      rcases max_choice a y with e | e
      · exact Or.inl e
      · exact Or.inr (by rw [e]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem vtH_n_ex (hr : H.rows.length = 6) : ∃ t < 6, vtHt H.rows t = H.n := by
  rcases vsFoldl_max_mem (tableHeightsOf H.rows) 0 with h | h
  · refine ⟨0, by norm_num, ?_⟩
    have := vtH_n_ge hr (t := 0) (by norm_num)
    unfold VtHonest.n at this ⊢; rw [h] at this ⊢; omega
  · rw [vt_tableHeights_eq hr] at h
    obtain ⟨t, ht, e⟩ := List.mem_map.mp h
    refine ⟨t, List.mem_range.mp ht, ?_⟩
    show vtHt H.rows t = (tableHeightsOf H.rows).foldl max 0
    rw [vt_tableHeights_eq hr]; exact e

theorem claimKappaSrc_code : ∀ j < 164, claimKappaSrc.getD j 0 =
    (if j < 4 then 1 else if j = 4 then 0 else vsEvTab (j - 5) + 2) := by decide +kernel

/-- **Each pooled honest claim's point has its low dimension.** -/
theorem ptsP_length (hr : H.rows.length = 6) (hlmμ : H.lm ≤ H.point.length)
    (h19 : 19 ≤ H.point.length) {j : ℕ} (hj : j < 164) :
    (H.ptsP j).length = claimLowDim H.lm (tableHeightsOf H.rows) j := by
  unfold claimLowDim ptsP
  rw [claimKappaSrc_code j hj]
  by_cases hj4 : j < 4
  · simp [hj4, claimKappaAdj, min_eq_left hlmμ]; omega
  by_cases hj5 : j = 4
  · subst hj5; simp [claimKappaAdj, min_eq_left h19]
  · have ht := vsEvTab_lt (j - 5) (by omega)
    simp only [hj4, hj5, hj, ↓reduceIte, List.length_take, chiW_length,
      min_eq_left (vtH_n_ge hr ht), claimKappaAdj, Nat.add_zero, List.getD_cons_succ]
    rfl

/-- **`verify_tables`' context, honestly.** -/
theorem vtH_tctx (h : H.Ok) (hr : H.rows.length = 6) (hbc : H.bc.length = 2 ^ 23)
    (hlmμ : H.lm ≤ H.point.length) (h19 : 19 ≤ H.point.length)
    (hτμ : ∀ t < 6, vtHt H.rows t ≤ H.point.length) {rd : Reader} {zeta chi : E}
    (hz : TbReadsAt rd zeta H.point) (hc : TbReadsAt rd chi H.chiW) :
    TCtx rd H.L H.bus H.claims [zeta, chi, H.rm, gen ^ H.point.length, gen ^ H.n] := by
  have hbus : H.bus = H.busH := (vt_spec h).2.1
  have hcol := vtH_columns h hr
  have hl : H.claims.length = 167 := by
    rw [← List.length_map (f := (·.column)), hcol]; decide +kernel
  obtain ⟨t, ht, htn⟩ := vtH_n_ex hr
  refine ⟨H.chiW, by rw [hbus]; exact hz, by rw [hbus]; rfl, hc, by rw [chiW_length],
    by rw [chiW_length, hbus, ← htn]; exact hτμ t ht, hl, hcol, fun j p hp ↦ ?_⟩
  rw [vtH_ptsP h hr hbc, List.getElem?_map] at hp
  have hj : j < 167 := by
    by_contra hn; rw [List.getElem?_eq_none (by simp; omega)] at hp; simp at hp
  rw [List.getElem?_range hj] at hp
  simp only [Option.map_some, Option.some.injEq] at hp
  subst hp
  rw [hbus]
  refine ⟨fun hj2 ↦ ptsP_length hr hlmμ h19 hj2, fun hj5 ↦ ?_, fun hj5 hj2 ↦ ?_, fun hj2 ↦ ?_⟩
  · show H.ptsP j = H.point.take (H.ptsP j).length
    unfold ptsP
    by_cases hj4 : j < 4
    · simp only [hj4, ↓reduceIte]; exact take_self_len _ _
    · simp only [show j = 4 by omega, ↓reduceIte]; exact take_self_len _ _
  · have hj2' : j < 164 := hj2
    unfold ptsP
    simp only [show ¬ j < 4 by omega, show j ≠ 4 by omega, hj2', ↓reduceIte]
    exact take_self_len _ _
  · have hj2' : 164 ≤ j := hj2
    unfold ptsP
    simp only [show ¬ j < 4 by omega, show j ≠ 4 by omega, show ¬ j < 164 by omega, ↓reduceIte]

end VtHonest

end
end LeanVM.Guest.B1.Tables
