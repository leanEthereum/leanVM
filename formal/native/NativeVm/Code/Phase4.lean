module

public import NativeVm.Code.Phase4.Tables
public import NativeVm.Code.Phase4.Next
public import NativeVm.Code.Phase4.Rounds
public import NativeVm.Code.Phase4.Target
public import NativeVm.Code.Phase4.Weights
public import NativeVm.Code.Phase4.Claims
public import NativeVm.Code.Phase4.Model
public import NativeVm.Code.Phase2.Kit

/-!
# Phase 4: the table sumcheck

The code of `Model.tablePhase` (`P4.phase4Code`), proved against it (`phase4_ok : Phase4Ok phase4`).

With its constants evaluated (`tablePhase_eq`), the phase is a chain of refinements: `ξ` sampled
(`P4.sampleChallenge_fr`), its powers and the target at the scratch's words (`targetC_spec`), the
rounds (`roundsC_refines`), the tables' weights (`weightsC_spec`), the tables' loop
(`termsC_refines`), `require (final == claim)` (`checkC_spec`), the column claims appended at
`claimsR` (`claimsC_spec`). Until the claims, every block writes only `evalsR` and `scratchR`, so the
phase's start survives in `Kept env rsT s0` and the layout, the bus and the claims are read from it
(`Kept.layoutAt`, `Kept.busAt`, `Kept.claimsAt`); each block's own facts ride in the stable
predicate of the next refinement (`RStab`, `TStab`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

/-- **Phase 4**: the table sumcheck. -/
def phase4 : Stmt := P4.phase4Code

namespace P4

variable {env : Env}

/-- The regions the phase writes before the column claims. -/
abbrev rsT : List Region := [evalsR, scratchR]

/-- The phase's regions. -/
abbrev rs4 : List Region := [evalsR, claimsR, scratchR]

theorem rsT_stop {n : Nat} : ∀ r ∈ rsT, r.stop ≤ workWords n :=
  fun r hr ↦ stop_le_of_mem (by revert r hr; decide +kernel) n

theorem rsT_rs4 : ∀ r ∈ rsT, r ∈ rs4 := by decide +kernel

section
variable {inp : Input} {s0 s : QState}

theorem Kept.layoutAt (hk : Kept env rsT s0 s) (hin : Inputs env inp s0.mem) {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} (h : LayoutAt s0.mem (layoutR.at env.work) bc layout rate) :
    LayoutAt s.mem (layoutR.at env.work) bc layout rate :=
  h.congr (hk.same hin rsT_stop (by decide +kernel) (by decide +kernel))

theorem Kept.busAt (hk : Kept env rsT s0 s) (hin : Inputs env inp s0.mem) {bus : BusResultW}
    (h : BusAt s0.mem (busR.at env.work) bus) : BusAt s.mem (busR.at env.work) bus :=
  h.congr (hk.same hin rsT_stop (by decide +kernel) (by decide +kernel))

theorem Kept.claimsAt (hk : Kept env rsT s0 s) (hin : Inputs env inp s0.mem)
    {acc : Array ColumnClaimW} (h : ClaimsAt s0.mem (claimsR.at env.work) acc) :
    ClaimsAt s.mem (wd env.work oC) acc := by
  rw [← claimsR_off]
  exact h.congr (hk.same hin rsT_stop (by decide +kernel) (by decide +kernel))

theorem Kept.ctxWork (hk : Kept env rsT s0 s) (hin : Inputs env inp s0.mem) {t : TState}
    (hc : CodeRel env t s0) : s.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
  rw [hk.ctx hin rsT_stop (by rw [scratchW_val]; decide), hc.layout.workPtr, wd_zero]

end

theorem heights_words {mem : UInt64 → Option UInt64} {bc : Array UInt64} {layout : LayoutW}
    {rate : Nat} (h : LayoutAt mem (layoutR.at env.work) bc layout rate) :
    ∀ i < 6, mem (wd env.work (oL + 4 + i)) = some (layout.tableLogHeights.getD i 0).toUInt64 :=
  fun i hi ↦ by
    have := (h.heights i hi).2
    rwa [Region.at, wd_wd, layoutR_off, ← Nat.add_assoc] at this

theorem forms_at {mem : UInt64 → Option UInt64} {bus : BusResultW}
    (h : BusAt mem (busR.at env.work) bus) :
    ∀ t < 6, ∀ side < 3, FormAt mem (wd env.work (oB + formsStride * t + fW * side))
      ((bus.forms.getD t #[]).getD side #[]) := fun t ht side hs ↦ by
  have := h.2.2.1 t ht side hs
  rw [Region.at, wd_wd, formOff_val] at this
  rwa [show oB + formsStride * t + fW * side = oB + fW * (3 * t + side) by
    simp only [formsStride, fW]; omega]

theorem claims_InRs : InRs [claimsR] (fun k ↦ oC ≤ k ∧ k < oC + claimsWords) := fun k hk ↦
  ⟨claimsR, by simp, by rw [claimsR_off]; exact hk.1, by
    show k < claimsR.off + claimsWords; rw [claimsR_off]; exact hk.2⟩

end P4

open P4 in
/-- **Phase 4 computes `tablePhase`.** -/
theorem phase4_ok : Phase4Ok phase4 := by
  intro env inp t s0 layout rate bus acc hc hin hlay hbus hcl hsz
  have h4 : Env4 env := Env4.of hin hc
  have hws0 : WS env s0 := WS.of fun k _ h2 ↦ hin.workSome k (lt_of_lt_of_le h2 (dataEnd_le _))
  have hhs : layout.tableLogHeights.size = 6 := hlay.heightsSize
  have hhb : ∀ i < 6, layout.tableLogHeights.getD i 0 ≤ 30 := hlay.heightsBound
  apply runs_of_refines
  rw [tablePhase_eq]
  unfold phase4 P4.phase4Code
  refine Refines.mono (P := fun t s ↦ CodeRel env t s ∧ (Kept env rsT s0 s ∧ WS env s)) ?_
    (fun t' s' ⟨e1, e2⟩ ↦ by subst e1 e2; exact ⟨hc, ⟨hc.rdi, fun _ _ _ ↦ rfl⟩, hws0⟩)
    (fun _ _ _ h ↦ h) (fun _ h ↦ h)
  -- `ξ`
  refine Refines.blk_cons ((P4.sampleChallenge_fr (R := fun s ↦ Kept env rsT s0 s ∧ WS env s)
      (Stab.keeps ((Stab.kept (ws := []) (by simp)).and (Stab.wsome [] clobbers))
        fun _ h ↦ h)).mono
      (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) fun _ h ↦ h.1.mono rsT_rs4) fun xi ↦ ?_
  -- `ξ`'s powers and the target
  refine Refines.pre_blk (P' := fun t s ↦ CodeRel env t s ∧
      (Kept env rsT s0 s ∧ EWArr s.mem (wd env.work oXP) (powers xi 5)) ∧ WS env s ∧
      s.mem (wd env.ctx ctxWork) = some (wd env.work 0) ∧
      (∀ i < 6, s.mem (wd env.work (oL + 4 + i)) = some (layout.tableLogHeights.getD i 0).toUInt64) ∧
      EWAt s.mem (wd env.work oCLM) (dot (fpOf xi) bus.totals))
    (fun t s ⟨hc1, ⟨hk1, hws1⟩, h9, h10⟩ ↦ ?_) ?_
  · have hb1 := Kept.busAt hk1 hin hbus
    have htot : EWArr s.mem (wd env.work oBT) bus.totals := by
      have := hb1.2.2.2.2.2; rwa [Region.at, wd_wd, busTotalsOff_val] at this
    refine WP.mono (WP.dom (targetC_spec h4 hk1.1 (Kept.ctxWork hk1 hin hc) hws1 xi h9 h10 bus.totals
      hb1.2.2.2.2.1 htot)) (fun s' ⟨⟨hp, hcl', w, rf⟩, d⟩ ↦ ?_) fun _ h ↦ h
    have hW : InRs [scratchR] (fun k ↦ oXP ≤ k ∧ k < oXP + 12) :=
      scratch_InRs fun j hj ↦ by simp only [oXP, oS] at hj; omega
    have hk' : Kept env rsT s0 s' :=
      Stab.kept (ws := [scratchR]) (by decide +kernel) s s' hk1 (Fr.ofWr w hW d rf (by decide))
    exact ⟨CodeRel.only hc1 h4 (by decide) (Only.ofWr w hW) d (rf .rdi (by decide)), ⟨hk', hp⟩,
      WS.wr hws1 d, Kept.ctxWork hk' hin hc, heights_words (Kept.layoutAt hk' hin hlay), hcl'⟩
  -- the rounds
  have hXR : RStab env (fun s ↦ Kept env rsT s0 s ∧ EWArr s.mem (wd env.work oXP) (powers xi 5)) :=
    fun s s' ⟨hk, hp⟩ hf hw ↦ ⟨Stab.kept (by decide +kernel) s s' hk hf,
      EWArr.wf hw hp (by simp only [oXP, oS]; omega) (by rw [powers_size]; simp only [oXP, oS]; omega)
        fun i hi ↦ by
          rw [powers_size] at hi; simp only [WR, oXP, oCLM, oMSG, oPT, oNR, oS]; omega⟩
  simp only [tableSumcheck]
  refine Refines.blk_cons ((roundsC_refines h4 hXR layout.tableLogHeights hhs hhb _).mono
    (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) fun _ h ↦ h.1.mono rsT_rs4) fun ⟨ch, cl⟩ ↦ ?_
  -- the weights
  have hnRb := foldl_max_le _ hhs hhb
  refine Refines.pre_blk (P' := fun t s ↦ ch.reverse.size = layout.tableLogHeights.foldl max 0 ∧
      (CodeRel env t s ∧
      (Kept env rsT s0 s ∧ EWArr s.mem (wd env.work oXP) (powers xi 5) ∧
        EWAt s.mem (wd env.work oCLM) cl) ∧ WS env s ∧
      (∀ i < 6, s.mem (wd env.work (oL + 4 + i)) = some (layout.tableLogHeights.getD i 0).toUInt64) ∧
      (∀ t < 6, ∀ side < 3, FormAt s.mem (wd env.work (oB + formsStride * t + fW * side))
        ((bus.forms.getD t #[]).getD side #[])) ∧
      EWArr s.mem (wd env.work oXP) (powers xi 5) ∧
      EWArr s.mem (wd env.work oWT) (tableWeights layout.tableLogHeights bus.point ch.reverse) ∧
      EWArr s.mem (wd env.work oPT) ch.reverse))
    (fun t s ⟨hc2, ⟨hk2, hp2⟩, hws2, _, _, _, _, hsz2, hcl2, hpt2, hnr2⟩ ↦ ?_) ?_
  · have hb2 := Kept.busAt hk2 hin hbus
    have heq : EVec s.mem (wd env.work oBP) busPointCap bus.point := by
      have := hb2.2.2.2.1; rwa [Region.at, wd_wd, busPointOff_val] at this
    have hsz2' : ch.reverse.size = layout.tableLogHeights.foldl max 0 := by
      rw [Array.size_reverse]; exact hsz2
    have hpt2' : EWArr s.mem (wd env.work oPT) ch.reverse := by simpa using hpt2
    refine WP.mono (WP.dom (weightsC_spec hk2.1 (Kept.ctxWork hk2 hin hc) hws2
      layout.tableLogHeights hhs (heights_words (Kept.layoutAt hk2 hin hlay)) hhb ch.reverse hsz2'
      (by rw [hsz2']; exact hnr2) hpt2' bus.point heq)) (fun s' ⟨⟨hw, w, rf⟩, d⟩ ↦ ?_) fun _ h ↦ h
    have hW : InRs [scratchR] (fun k ↦ oWT ≤ k ∧ k < oWT + 12) :=
      scratch_InRs fun j hj ↦ by simp only [oWT, oS] at hj; omega
    have hk' : Kept env rsT s0 s' :=
      Stab.kept (ws := [scratchR]) (by decide +kernel) s s' hk2 (Fr.ofWr w hW d rf (by decide))
    have hp' : EWArr s'.mem (wd env.work oXP) (powers xi 5) :=
      EWArr.wr w hp2 (by rw [powers_size]; simp only [oXP, oS]; omega) fun k hk ↦ by
        rw [powers_size]; simp only [oXP, oWT, oS] at hk ⊢; omega
    exact ⟨hsz2', CodeRel.only hc2 h4 (by decide) (Only.ofWr w hW) d (rf .rdi (by decide)),
      ⟨hk', hp', EWAt.wr w hcl2 (by simp only [oCLM, oS]; omega) fun k hk ↦ by
        simp only [oCLM, oWT, oS] at hk ⊢; omega⟩,
      WS.wr hws2 d, heights_words (Kept.layoutAt hk' hin hlay), forms_at (Kept.busAt hk' hin hbus),
      hp', hw, EWArr.wr w hpt2' (by rw [hsz2']; simp only [oPT, oS]; omega) fun k hk ↦ by
        rw [hsz2']; simp only [oPT, oWT, oS] at hk ⊢; omega⟩
  -- the tables
  refine Refines.intro fun hps ↦ ?_
  have hXT : TStab env (fun s ↦ Kept env rsT s0 s ∧ EWArr s.mem (wd env.work oXP) (powers xi 5) ∧
      EWAt s.mem (wd env.work oCLM) cl) :=
    fun s s' ⟨hk, hp, hcl⟩ hf hw ↦ ⟨Stab.kept (by decide +kernel) s s' hk hf,
      EWArr.wf hw hp (by simp only [oXP, oS]; omega) (by rw [powers_size]; simp only [oXP, oS]; omega)
        (fun i hi ↦ by
          rw [powers_size] at hi; simp only [WT, oXP, oE, oFIN, oCV, oTIX, oWID, oS]; omega),
      EWAt.wf hw hcl (by simp only [oCLM, oS]; omega) (by simp only [oCLM, oS]; omega)
        (by simp only [WT, oCLM, oE, oFIN, oCV, oTIX, oWID, oS]; omega)⟩
  refine Refines.blk_cons ((termsC_refines h4 hXT layout.tableLogHeights hhs hhb bus.forms hbus.1
    hbus.2.1 xi ch.reverse hps _ (by rw [tableWeights_size, hhs])).mono
    (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) fun _ h ↦ h.1.mono rsT_rs4) fun ⟨fin, ev⟩ ↦ ?_
  -- `final == claim`
  refine Refines.blk_cons (Q₁ := fun _ t s ↦ CodeRel env t s ∧ Kept env rsT s0 s ∧ WS env s ∧
      EvalsAt s.mem (wd env.work oE) ev ∧ ∀ t < 6, (ev.getD t (#[], #[])).2.size = widths.getD t 0)
    (Refines.require fun t s ⟨hc3, ⟨hk3, _, hcl3⟩, hws3, hfin, hev, hwid⟩ ↦
      WP.mono (checkC_spec hk3.1 (Kept.ctxWork hk3 hin hc) hfin hcl3)
        (fun s' ⟨hb, hm, rf⟩ ↦ ⟨hb, CodeRel.only (ws := []) hc3 h4 (by decide) (fun _ _ ↦ by rw [hm])
          (DomEq.ofEq hm) (rf .rdi (by decide)),
          ⟨(rf .rdi (by decide)).trans hk3.1, fun a hf hr ↦ by rw [hm]; exact hk3.2 a hf hr⟩,
          WS.wr hws3 (DomEq.ofEq hm), by rw [hm]; exact hev, hwid⟩)
        fun s' ⟨hb, hm, rf⟩ ↦ ⟨hb, Kept.mono (rs := rsT)
          ⟨(rf .rdi (by decide)).trans hk3.1, fun a hf hr ↦ by rw [hm]; exact hk3.2 a hf hr⟩
          rsT_rs4⟩) fun _ ↦ ?_
  -- the column claims
  refine Refines.pure fun t s ⟨hc4, hk4, hws4, hev4, hwid4⟩ ↦
    WP.mono (WP.dom (claimsC_spec hk4.1 (Kept.ctxWork hk4 hin hc) hws4 ev acc hev4 hwid4
      (Kept.claimsAt hk4 hin hcl) hsz)) (fun s' ⟨⟨hcl', w, rf⟩, d⟩ ↦ ?_) fun _ h ↦ h
  have hWF : WF env (fun k ↦ oC ≤ k ∧ k < oC + claimsWords) s s' :=
    WF.ofWr w fun k hk ↦ by rw [claimsWords_val] at hk; simp only [oC] at hk; omega
  have hS := hWF.same (q := evalsR) (by rw [evalsR_off]; simp only [oE]; omega)
    (by rw [evalsR_off, evalsR_size]; simp only [oE]; omega) fun k hk ↦ by
      rw [evalsR_off, evalsR_size]; rw [claimsWords_val] at hk; simp only [oC, oE] at hk ⊢; omega
  have hev' : EvalsAt s.mem (evalsR.at env.work) ev := by rw [Region.at, evalsR_off]; exact hev4
  exact ⟨CodeRel.only hc4 h4 (by decide) (Only.ofWr w claims_InRs) d (rf .rdi (by decide)),
    ⟨hev'.congr hS, by rw [Region.at, claimsR_off]; exact hcl', by
      rw [tableColumnClaims_size hev4.1 hwid4]; decide⟩,
    Stab.kept (ws := [claimsR]) (by decide +kernel) s s' (Kept.mono hk4 rsT_rs4)
      (Fr.ofWr w claims_InRs d rf (by decide))⟩

/-- info: 'NativeVm.Code.phase4_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase4_ok

end NativeVm.Code
