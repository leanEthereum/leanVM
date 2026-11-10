import Rv64Verifier.Proofs.Pcs.VsoFinalBasis

/-!
# `verify_stacked_opening`'s final level: the tail up to the terminal check

At `0x8000bab0`, with no glued claim the weight is the basis's and the tail goes on to the
terminal check (`tEmpty`); otherwise the glued claims' loop (`GluedSpec`) runs first.
`toCheck_of` chains the rounds, the point, the basis and the glue into `ToCheck`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Every glued claim at its suffix of the point, from the basis's weight `w0`. -/
def gluedFold (glued : List Model.Pcs.GluedClaimRust) (point : List E) (w0 : E) : Option E :=
  glued.foldlM (fun weight claim ↦ do
    let x ← Model.Pcs.sliceFrom claim.foldStart point
    let value ← claim.weight.evaluate x
    pure (weight + claim.scalar * value)) w0

theorem cfg_fold0 (s : MachineState) : (cfgOf s).folds[0]? = some 6 := rfl

/-- What is left of the mirror once the basis is known. -/
theorem afterTail_basis (s : MachineState) (basis : List E → Option E) (residual : List E)
    (Wl : Model.Pcs.WhirLocals) (tf : List E) (rt w0 : E) (h6 : 6 ≤ (Wl.folds ++ tf).length)
    (hb : basis ((Wl.folds ++ tf).drop 6 ++ (Wl.folds ++ tf).take 6) = some w0) :
    afterTail (cfgOf s) basis residual Wl tf rt =
      Model.TM.ofOption (gluedFold Wl.glued (Wl.folds ++ tf) w0) >>= fun w ↦
        terminalCheckM residual tf w rt := by
  unfold afterTail Model.Pcs.terminalWeightRust gluedFold
  rw [cfg_fold0, show Model.TM.ofOption (some 6) = (pure 6 : Model.TM ℕ) from rfl, pure_bind]
  have e : (do
      let high ← Model.Pcs.sliceFrom 6 (Wl.folds ++ tf)
      let low ← Model.Pcs.sliceTo 6 (Wl.folds ++ tf)
      let weight ← basis (high ++ low)
      Wl.glued.foldlM (fun weight claim ↦ do
        let x ← Model.Pcs.sliceFrom claim.foldStart (Wl.folds ++ tf)
        let value ← claim.weight.evaluate x
        pure (weight + claim.scalar * value)) weight) =
      Wl.glued.foldlM (fun weight claim ↦ do
        let x ← Model.Pcs.sliceFrom claim.foldStart (Wl.folds ++ tf)
        let value ← claim.weight.evaluate x
        pure (weight + claim.scalar * value)) w0 := by
    simp only [Model.Pcs.sliceFrom, Model.Pcs.sliceTo, h6, ↓reduceIte]
    show basis _ >>= _ = _
    rw [hb]; rfl
  rw [e]

/-- The glued claims' loop: from `0x8000bab0` with claims to glue, to the terminal check. -/
def GluedSpec (OA : MachineState → Word → Model.TState → Prop) : Prop :=
  ∀ s x u v Wl residual tf rt w0, VsoPre s → TB OA s x u v Wl residual tf rt w0 →
    (vecLen v (s.getReg .x2 - 664)).toNat ≠ 0 →
    ∃ w, Reaches Image.code v w ∧ (FailR s w ∨ ∃ ml res tf' wt rt', TC OA s w ml res tf' wt rt')

/-- No glued claim: from `0x8000bab0` straight to the terminal check. -/
theorem tEmpty {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E}
    (hpre : VsoPre s) (h : TB OA s x u v Wl residual tf rt w0)
    (h0 : (vecLen v (s.getReg .x2 - 664)).toNat = 0) :
    ∃ w, Reaches Image.code v w ∧ TC OA s w (mlF s Wl) residual tf w0 rt := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.sp
  have hfin := h.toTI.fin
  have hlen0 : vecLen v (s.getReg .x2 - 664) = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [h0]; rfl
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bab0_spec h.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have k₁ := b8000bab0_keeps h₁
  have hm₁ := b8000bab0_mem_same h₁
  obtain ⟨T₁, -⟩ := h.toTI.stepS hpre (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₁ .x2 (by decide))
  have hpc : t₁.pc = 0x8000bfe8 := b8000bab0_pc_taken h₁ (by
    rw [hsp, show s.getReg .x2 - BitVec.ofNat 64 1040 + 392 = s.getReg .x2 - 664 + 16 by
      addr_omega [hb]]; exact hlen0)
  -- no glued claim
  have hgl : Wl.glued = [] := by
    have hg := hfin.glued.2.1
    have e : vecLen u (s.getReg .x2 - 664) = vecLen v (s.getReg .x2 - 664) := by
      simp only [vecLen]; exact (h.toTI.keepStk hpre (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)).symm
    rw [e, hlen0] at hg
    rw [← hg]; rfl
  have hml := logN_le hfin.cfg
  obtain ⟨hTv, hTe, hTn⟩ := h.tail
  have hTl := TailV.len h.tail
  rw [h.tfl] at hTl
  have hTc := hTv.len
  have hres := hfin.res
  have hsL := hfin.hs
  have hrb : (u.getMem (s.getReg .x2 - 960)).toNat = 0 ∨
      heapNext s ≤ (u.getMem (s.getReg .x2 - 968)).toNat ∧
      (u.getMem (s.getReg .x2 - 968)).toNat + 24 * (u.getMem (s.getReg .x2 - 960)).toNat ≤
        heapNext u := by
    rcases hres.2.2 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, h0.2⟩
  have k968 : t₁.getMem (s.getReg .x2 - 968) = u.getMem (s.getReg .x2 - 968) :=
    T₁.keepStk hpre (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)
  have k960 : t₁.getMem (s.getReg .x2 - 960) = u.getMem (s.getReg .x2 - 960) :=
    T₁.keepStk hpre (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)
  have hn₁ : heapNext t₁ = heapNext v := by simp only [heapNext, hm₁]
  have hvm := h.mono
  have hum := T₁.mono
  refine ⟨t₁, r₁, {
    inv := T₁.inv hpre
    heap := T₁.heap
    pc := hpc
    ml64 := by simp only [mlF]; omega
    x19 := by rw [k₁ .x19 (by decide), h.x19]
    tail := by
      rw [k₁ .x8 (by decide), h.x8, show vecPtr v (s.getReg .x2 - 304) = vecPtr t₁ (s.getReg .x2 - 304)
        by simp only [vecPtr]; rw [hm₁]]
      refine ⟨?_, ?_, ?_⟩
      · rw [← hTe, ← hTl]; simp only [vecEs, eListAt, eAt, vecPtr, hm₁]
      · simp only [vecPtr, hm₁]; exact hTv.raw.1
      · simp only [vecPtr, hm₁]
        rcases hTn.2 with h0 | h0
        · left; omega
        · right; simp only [vecPtr] at h0; rw [hn₁]; exact ⟨by have := hfin.su; omega, by omega⟩
    res := by
      rw [k968, k960, T₁.eList hpre hrb]
      refine ⟨hres.1, hres.2.1, ?_⟩
      rcases hrb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by omega⟩
    rlen := hfin.rlen
    wt := by rw [show eAt t₁ (s.getReg .x2 - 184) = eAt v (s.getReg .x2 - 184) by
      simp only [eAt, hm₁]]; exact h.wt
    trg := by simp only [hm₁]; exact h.trg
    value := by
      have hv := h.value
      rw [afterTail_basis s _ _ _ _ _ _ h.six h.basis, hgl] at hv
      exact hv.keep hpre (h.toTI.inv hpre) (DFrame.of_same hm₁ (fun _ ↦ False)) fun _ h ↦ h.elim }⟩

/-- **The tail up to the terminal check**, from the glued claims' loop. -/
theorem toCheck_of (hD : DuplexSpec) (hPE : PolyEvalSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8)
    (hRP : RoundPolyErrSpec) (hC : MultilinearContracts.SliceConcatSpec) (hB : BasisSpec)
    {OA : MachineState → Word → Model.TState → Prop} (hGl : GluedSpec OA) :
    ToCheck OA := by
  intro s x u Wl residual hpre hin
  obtain ⟨v₁, r₁, h₁⟩ := tRounds hD hPE hG hRP hpre hin
  rcases h₁ with hf | ⟨tf, rt, ha⟩
  · exact ⟨v₁, r₁, Or.inl hf⟩
  obtain ⟨v₂, r₂, h₂⟩ := tPoint hC hpre ha
  rcases h₂ with hd | hv
  · exact ⟨v₂, r₁.trans r₂, Or.inl (Or.inl hd)⟩
  obtain ⟨v₃, r₃, h₃⟩ := tBasis hB hpre hv
  rcases h₃ with hd | ⟨w0, htb⟩
  · exact ⟨v₃, r₁.trans (r₂.trans r₃), Or.inl (Or.inl hd)⟩
  by_cases h0 : (vecLen v₃ (s.getReg .x2 - 664)).toNat = 0
  · obtain ⟨w, rw', hw⟩ := tEmpty hpre htb h0
    exact ⟨w, r₁.trans (r₂.trans (r₃.trans rw')), Or.inr ⟨_, _, _, _, _, hw⟩⟩
  · obtain ⟨w, rw', hw⟩ := hGl s x u v₃ Wl residual tf rt w0 hpre htb h0
    exact ⟨w, r₁.trans (r₂.trans (r₃.trans rw')), hw⟩

end Rv64Verifier.Proofs.Pcs.Vso
