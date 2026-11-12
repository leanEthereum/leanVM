/-
  LeanVM.Guest.B1.VerifySub.H.TermCtx

  What `check_opening_terminal` takes of an honest child's claims: `verify_tables`' context
  (`TCtx`) on a memory holding the bus point and `chi`.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Claims

/-!
# The terminal's context

`ptsP H j`: honest claim `j`'s point (the bus point cut to `logMemory` three times, to `19` once,
`chi` cut to evaluation `j - 4`'s table's height, the public input's point); `vtH_ptsP`: the
honest claims' points are those. `vtH_tctx`: on a memory holding the bus point at `zeta` and
`chi`'s words, `TCtx` holds of the honest layout, bus result and claims (each pooled claim's
point has the low dimension `claimLowDim` the terminal derives from `kappa_base`).
`ChildSegs.H_tctx`: the same on an honest child's segments; `ChildSegs.nT_le`: the table
sumcheck has at most `28` rounds.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace VtHonest

/-- Honest claim `j`'s point. -/
noncomputable def ptsP (H : VtHonest) (j : ℕ) : List E :=
  if j < 3 then H.point.take H.lm else if j = 3 then H.point.take 19
  else if j < 157 then H.chiW.take (vtHt H.rows (vsEvTab (j - 4)))
  else H.rm :: List.replicate ((H.L.placement memory0).variableCount - 1) 0

variable {H : VtHonest}

theorem vtH_ptsP (h : H.Ok) (hr : H.rows.length = 6) (hbc : H.bc.length = 2 ^ 23) :
    H.claims.map (·.point) = (List.range 159).map H.ptsP := by
  rw [vtH_points h hr hbc]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_map, List.getElem_range, ptsP]
  by_cases hj3 : j < 3
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simp; omega)]
    simp only [hj3, ↓reduceIte]
    interval_cases j <;> rfl
  by_cases hj4 : j = 3
  · subst hj4
    rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp)]
    simp
  by_cases hj157 : j < 157
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil,
      List.getElem_map, List.getElem_range, hj3, hj4, hj157, ↓reduceIte]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_replicate, hj3, hj4, hj157, ↓reduceIte]

theorem take_self_len (l : List E) (k : ℕ) : l.take k = l.take (l.take k).length := by
  rw [List.length_take]; exact List.take_eq_take_min

theorem chiW_length (H : VtHonest) : H.chiW.length = H.n := by
  simp [VtHonest.chiW, zcChis]

theorem vsEvTab_lt : ∀ k < 153, vsEvTab k < 6 := by decide +kernel

theorem vtH_n_ex (hr : H.rows.length = 6) : ∃ t < 6, vtHt H.rows t = H.n := by
  rcases foldl_max_mem (tableHeightsOf H.rows) 0 with h | h
  · refine ⟨0, by norm_num, ?_⟩
    have := vt_n_ge hr (H := H) (t := 0) (by norm_num)
    have e : H.n = 0 := h
    show vtHt H.rows 0 = H.n
    unfold VtHonest.τ at this
    omega
  · rw [vt_tableHeights_eq hr] at h
    obtain ⟨t, ht, e⟩ := List.mem_map.mp h
    refine ⟨t, List.mem_range.mp ht, ?_⟩
    show vtHt H.rows t = (tableHeightsOf H.rows).foldl max 0
    rw [vt_tableHeights_eq hr]; exact e

theorem claimKappaSrc_code : ∀ j < 157, claimKappaSrc.getD j 0 =
    (if j < 3 then 1 else if j = 3 then 0 else vsEvTab (j - 4) + 2) := by decide +kernel

/-- **Each pooled honest claim's point has its low dimension.** -/
theorem ptsP_length (hr : H.rows.length = 6) (hlmμ : H.lm ≤ H.point.length)
    (h19 : 19 ≤ H.point.length) {j : ℕ} (hj : j < 157) :
    (H.ptsP j).length = claimLowDim H.lm (tableHeightsOf H.rows) j := by
  unfold claimLowDim ptsP
  rw [claimKappaSrc_code j hj]
  by_cases hj3 : j < 3
  · simp [hj3, claimKappaAdj, min_eq_left hlmμ]; omega
  by_cases hj4 : j = 3
  · subst hj4; simp [claimKappaAdj, min_eq_left h19]
  · have ht := vsEvTab_lt (j - 4) (by omega)
    have hn := vt_n_ge hr (H := H) ht
    unfold VtHonest.τ at hn
    simp only [hj3, hj4, hj, ↓reduceIte, List.length_take, chiW_length,
      min_eq_left hn, claimKappaAdj, Nat.add_zero, List.getD_cons_succ]
    rfl

/-- **`verify_tables`' context, honestly.** -/
theorem vtH_tctx (h : H.Ok) (hr : H.rows.length = 6) (hbc : H.bc.length = 2 ^ 23)
    (hlmμ : H.lm ≤ H.point.length) (h19 : 19 ≤ H.point.length)
    (hτμ : ∀ t < 6, vtHt H.rows t ≤ H.point.length) {rd : Reader} {zeta chi : E}
    (hz : TbReadsAt rd zeta H.point) (hc : TbReadsAt rd chi H.chiW) :
    TCtx rd H.L H.bus H.claims [zeta, chi, H.rm, gen ^ H.point.length, gen ^ H.n] := by
  have hbus : H.bus = H.busH := (vt_spec h).2.2.1
  have hcol := vtH_columns h hr
  have hl : H.claims.length = 159 := by
    rw [← List.length_map (f := (·.column)), hcol]; decide +kernel
  obtain ⟨t, ht, htn⟩ := vtH_n_ex hr
  refine ⟨H.chiW, by rw [hbus]; exact hz, by rw [hbus]; rfl, hc, by rw [chiW_length],
    by rw [chiW_length, hbus, ← htn]; exact hτμ t ht, hl, hcol, fun j p hp ↦ ?_⟩
  rw [vtH_ptsP h hr hbc, List.getElem?_map] at hp
  have hj : j < 159 := by
    by_contra hn; rw [List.getElem?_eq_none (by simp; omega)] at hp; simp at hp
  rw [List.getElem?_range hj] at hp
  simp only [Option.map_some, Option.some.injEq] at hp
  subst hp
  rw [hbus]
  refine ⟨fun hj2 ↦ ptsP_length hr hlmμ h19 hj2, fun hj5 ↦ ?_, fun hj5 hj2 ↦ ?_, fun hj2 ↦ ?_⟩
  · have hj5' : j < 4 := hj5
    show H.ptsP j = H.point.take (H.ptsP j).length
    unfold ptsP
    by_cases hj3 : j < 3
    · simp only [hj3, ↓reduceIte]; exact take_self_len _ _
    · simp only [show j = 3 by omega, ↓reduceIte]; exact take_self_len _ _
  · have hj2' : j < 157 := hj2
    have hj5' : 4 ≤ j := hj5
    unfold ptsP
    simp only [show ¬ j < 3 by omega, show j ≠ 3 by omega, hj2', ↓reduceIte]
    exact take_self_len _ _
  · have hj2' : 157 ≤ j := hj2
    unfold ptsP
    simp only [show ¬ j < 3 by omega, show j ≠ 3 by omega, show ¬ j < 157 by omega, ↓reduceIte]

end VtHonest

end
end LeanVM.Guest.B1.Tables

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The table sumcheck has at most `28` rounds. -/
theorem nT_le (hbl : bytecode.length = 2 ^ 23) : S.nT ≤ 30 := by
  rcases Tables.foldl_max_mem S.hs 0 with h | h
  · show S.hs.foldl max 0 ≤ 30
    omega
  · have := (S.hs_bounds hbl).1 _ h
    show S.hs.foldl max 0 ≤ 30
    omega

/-- **`verify_tables`' context on an honest child**, on a memory holding the bus point at `zeta`
and `chi`'s words. -/
theorem H_tctx (hbl : bytecode.length = 2 ^ 23) {rd : Reader} {zeta chi : E}
    (hz : Tables.TbReadsAt rd zeta S.rG.2.1) (hc : Tables.TbReadsAt rd chi S.H.chiW) :
    Tables.TCtx rd S.layout S.bus S.claims [zeta, chi, S.H.rm, gen ^ S.d, gen ^ S.nT] := by
  obtain ⟨h, -, -, -⟩ := S.H_run hbl
  have hs := S.H_shape hbl
  obtain ⟨-, -, -, -, hpl, -⟩ := S.gkr_inv hbl
  have e := Tables.VtHonest.vtH_tctx h hs.hr hs.hbc hs.hlmμ hs.h19 hs.hτμ hz hc
  have hL : S.H.L = S.layout := S.hlayout.symm
  rw [hL] at e
  have hp : S.H.point.length = S.d := hpl
  rw [hp] at e
  exact e

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
