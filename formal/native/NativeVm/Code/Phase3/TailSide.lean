module

public import NativeVm.Code.Phase3.TailVals2
public import NativeVm.Code.Phase3.SelSpec
public import NativeVm.Code.Phase3.Forms
public import NativeVm.Code.Phase3.Totals

/-!
# Phase 3 after the transcript: a side

`tl_side`: `sideCode side` (its selectors, forms and total) from the forms before, the side's forms
empty, its fingerprints and tree value, gives `accumulateSide`'s forms in `busR` and its total at
`totW side` (`tlAcc`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {s : QState}

/-- `accumulateSide` for side `side`, its arguments by side. -/
def tlAcc (forms : Array (Array FormW)) (side : Nat) (layout : LayoutW) (weights : Array EW)
    (beta : EW) (point ffp : Array EW) (tv : EW) : Array (Array FormW) × EW :=
  accumulateSide forms side (sideBlocks layout side) (sideLayout layout side) ffp
    (sideWeights weights side) (sideBeta beta side) point tv

/-- The regions a side's code writes. -/
def tlSW (side : Nat) : List Region :=
  [tselR side, padWR side, fselR side, tmpR, busR, sumR side, formTmpR, ⟨sSum, 8⟩, ⟨totW side, 2⟩]

theorem tl_tselR (side : Nat) : tselR side = ⟨53182 + 512 * side, 102⟩ := by
  rw [show tselR side = ⟨(tselR side).off, 102⟩ from rfl, fs_tselR_off]
theorem tl_padWR (side : Nat) : padWR side = ⟨53284 + 512 * side, 102⟩ := by
  rw [show padWR side = ⟨(padWR side).off, 102⟩ from rfl, fs_padWR_off, fs_tselR_off]; congr 1; omega
theorem tl_fselR (side : Nat) : fselR side = ⟨53386 + 512 * side, 6⟩ := by
  rw [show fselR side = ⟨(fselR side).off, 6⟩ from rfl, fselR_off]
theorem tl_sumR (side : Nat) : sumR side = ⟨54462 + 8 * side, 8⟩ := by
  rw [show sumR side = ⟨(sumR side).off, 8⟩ from rfl, sumR_off]
theorem tl_tmpR : tmpR = ⟨54718, 6144⟩ := by
  rw [show tmpR = ⟨tmpR.off, 6144⟩ from rfl, show tmpR.off = 54718 by
    show scratchR.off + 2048 = _; rw [scratchR_off]]
theorem tl_formTmpR : formTmpR = ⟨60862, 24576⟩ := by
  rw [show formTmpR = ⟨formTmpR.off, 24576⟩ from rfl, formTmpR_off]
theorem tl_busR : busR = ⟨622, 13471⟩ := by
  rw [show busR = ⟨busR.off, busR.size⟩ from rfl, busR_off, busR_size]

/-- Disjointness and bounds of literal regions, `side < 3` in the context. -/
scoped macro "tl_rg" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, tl_tselR,
    tl_padWR, tl_fselR, tl_sumR, tl_tmpR, tl_formTmpR, tl_busR, Region.stop, sl, totW, fselW, fpW,
    tselW, padW, tvW] <;> omega))

theorem tlSW_within {side : Nat} (hside : side < 3) : ∀ r ∈ tlSW side, ∃ q ∈ tlW, Within r q := by
  simp only [tlSW, tl_tselR, tl_padWR, tl_fselR, tl_sumR, tl_tmpR, tl_formTmpR, tl_busR]
  interval_cases side <;> decide

theorem tl_busAt : busR.at env.work = wd env.work 622 := by rw [Region.at, busR_off]

theorem tl_formsAt {ws : List Region} {s' : QState} {forms : Array (Array FormW)}
    (hw : Wrote env ws s s') (hc : ∀ r ∈ ws, 622 + 13338 ≤ r.off ∨ r.stop ≤ 622)
    (hws : ∀ r ∈ ws, r.stop ≤ 2 ^ 61) (hf : FormsAt s.mem (busR.at env.work) forms) :
    FormsAt s'.mem (busR.at env.work) forms := by
  refine hf.congr ?_
  rw [tl_busAt, show formWords * (3 * nTables) = 13338 from rfl]
  exact tl_same hw hc (by norm_num) hws

theorem tl_getD {xs : Array EW} {i : Nat} (h : i < xs.size) : xs.getD i 0 = xs[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

/-- **A side**: its selectors, forms and total. -/
theorem tl_side {side : Nat} (hside : side < 3) {layout : LayoutW} {rate : Nat}
    {point weights trees memory : Array EW} {beta mf bf share : EW}
    {forms : Array (Array FormW)} {ffp : Array EW}
    (h : TlIn env inp layout rate point weights trees memory beta mf bf share s)
    (hps : point.size < 64) (hws : weights.size = 16) (hts : trees.size = 3) (hms : memory.size = 2)
    (hf : FormsAt s.mem (busR.at env.work) forms)
    (he : ∀ t < nTables, (forms.getD t #[]).getD side #[] = #[])
    (hzero : EWAt s.mem (wd env.work sZero) 0) (hone : EWAt s.mem (wd env.work sOne) 1)
    (hfp : EWArr s.mem (wd env.work (fpW side)) ffp) (hfpz : ffp.size = if side = 2 then 0 else 3) :
    WP (blk [selCode side, formsCode side, totalCode side]) s (fun s' ↦
      FormsAt s'.mem (busR.at env.work)
        (tlAcc forms side layout weights beta point ffp (trees.getD side 0)).1 ∧
      EWAt s'.mem (wd env.work (totW side))
        (tlAcc forms side layout weights beta point ffp (trees.getD side 0)).2 ∧
      Wrote env (tlSW side) s s') (fun _ ↦ False) := by
  obtain ⟨rows, -, -, hbb⟩ := h.lay.rows
  obtain ⟨hTs, hFs⟩ := sideLayout_sizes layout side
  have hBs := sideBlocks_size hbb hside
  have hoffs := offs_eq hside
  have hb61 : ∀ r ∈ tlSW side, r.stop ≤ 2 ^ 61 := by simp only [tlSW]; tl_rg
  -- the selectors
  refine wp_then (sel_spec hside h.rdi h.wp h.hin h.lay h.sides
    (by rw [Region.at, pc_depthR_off]; exact h.depth) hps
    (by rw [Region.at, pc_pointR_off]; exact h.pt)) fun s1 ⟨tsel, pw, fs, w1⟩ ↦ ?_
  have ws1 : ∀ r ∈ [tselR side, padWR side, fselR side, tmpR], r ∈ tlSW side := by
    intro r hr; simp only [tlSW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
  have w1s : Wrote env (tlSW side) s s1 := w1.mono ws1
  have h1 := h.keep hps hws hts hms (tl_widen w1s (tlSW_within hside))
  have hb1 : ∀ r ∈ [tselR side, padWR side, fselR side, tmpR], r.stop ≤ 2 ^ 61 :=
    fun r hr ↦ hb61 r (ws1 r hr)
  -- the forms
  refine wp_then (forms_spec (weights := weights) (beta := beta) hside h1.rdi h1.wp h1.hin h1.lay
    (tl_formsAt w1 (by tl_rg) hb1 hf) he tsel (by rw [Array.size_map, hTs]) pw
    (by rw [padWeights, Array.size_map])
    (fun _ ↦ ⟨by rw [Region.at, wR_off]; exact h1.w, by rw [hws]; rfl⟩)
    (fun _ ↦ by rw [Region.at, betaR_off]; exact h1.beta)) fun s2 ⟨fm, sm, w2⟩ ↦ ?_
  have ws2 : ∀ r ∈ [busR, sumR side, tmpR, formTmpR], r ∈ tlSW side := by
    intro r hr; simp only [tlSW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
  have w2s : Wrote env (tlSW side) s s2 := w1s.trans (w2.mono ws2)
  have h2 := h.keep hps hws hts hms (tl_widen w2s (tlSW_within hside))
  have hb2 : ∀ r ∈ [busR, sumR side, tmpR, formTmpR], r.stop ≤ 2 ^ 61 :=
    fun r hr ↦ hb61 r (ws2 r hr)
  -- the total
  set fsels := (sideLayout layout side).framework.map (eqAbove · point)
  set tsels := (sideLayout layout side).tables.map (eqAbove · point)
  have hfsz : fsels.size = if side = 2 then 0 else 3 := by rw [Array.size_map, hFs]
  rw [Region.at, hoffs.2.1] at fs
  rw [Region.at, hoffs.2.2.1] at tsel
  rw [Region.at, hoffs.2.2.2.1] at sm
  refine WP.mono (totalCode_spec (β := sideBeta beta side) hside h2.rdi h2.wp h2.hin
    (tl_ewat w2 (by tl_rg) (by decide) hb2 (tl_ewat w1 (by tl_rg) (by decide) hb1 hzero))
    (tl_ewat w2 (by tl_rg) (by decide) hb2 (tl_ewat w1 (by tl_rg) (by decide) hb1 hone))
    (by have := h2.trees side (by omega); rwa [wd_wd, ← tl_getD (by omega)] at this)
    (fun h2' ↦ by
      rw [show sideBeta beta side = beta by unfold sideBeta; simp [show side ≠ 2 by omega]]
      exact h2.beta)
    (tl_ewarr w2 (n := 6) (by tl_rg) (by unfold fselW; omega) hb2 (by rw [hfsz]; split <;> omega) fs) hfsz
    (tl_ewarr w2 (n := 6) (by tl_rg) (by unfold fpW; omega) hb2 (by rw [hfpz]; split <;> omega)
      (tl_ewarr w1 (n := 6) (by tl_rg) (by unfold fpW; omega) hb1 (by rw [hfpz]; split <;> omega) hfp))
    (by rw [hfpz, hfsz])
    (tl_ewarr w2 (n := 102) (by tl_rg) (by unfold tselW; omega) hb2
      (by rw [Array.size_map, hTs, hBs]; unfold sideNb; split <;> omega) tsel)
    (by rw [Array.size_map, hTs, hBs]; rfl) sm) ?_ fun _ h ↦ h
  rintro s3 ⟨tot, w3⟩
  have hsplit := accumulateSide_split forms side (sideBlocks layout side) (sideLayout layout side)
    ffp (sideWeights weights side) (sideBeta beta side) point (trees.getD side 0)
  refine ⟨?_, ?_, w2s.trans (w3.mono fun r hr ↦ ?_)⟩
  · rw [tlAcc, hsplit]
    exact tl_formsAt w3 (by tl_rg) (by tl_rg) fm
  · rw [tlAcc, hsplit]
    exact tot
  · simp only [tlSW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto

end NativeVm.Code.P3
