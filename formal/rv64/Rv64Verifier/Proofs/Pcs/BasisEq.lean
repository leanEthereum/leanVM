import Rv64Verifier.Proofs.Pcs.BasisEval

/-!
# `<StackBasis>::evaluate`: an `Eq` weight, `eq_eval(point, x)` at `0x8000d164`
-/

namespace Rv64Verifier.Proofs.Pcs.Basis
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F55
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The `Eq` weight's point, read. -/
theorem eq_src {s : MachineState} (hpre : BasisPre s) {k : Nat} (hk : k < ncl s)
    (htag : s.getMem (claimAddr s k) = eqTag) :
    Src s basisStack (s.getMem (claimAddr s k + 16)) (24 * (s.getMem (claimAddr s k + 24)).toNat) := by
  have h1 : WeightSrc s basisStack (claimAddr s k) := hpre.weights k hk
  have h2 := h1.2
  change (if s.getMem (claimAddr s k) = eqTag then _ else _) at h2
  rw [ite_pos' htag] at h2
  have e8 : vecPtr s (claimAddr s k + 8) = s.getMem (claimAddr s k + 16) := by
    show s.getMem (claimAddr s k + 8 + 8) = _; rv_eval []
  have e16 : vecLen s (claimAddr s k + 8) = s.getMem (claimAddr s k + 24) := by
    show s.getMem (claimAddr s k + 8 + 16) = _; rv_eval []
  rw [e8, e16] at h2
  exact h2

theorem eq_weight {s : MachineState} {k : Nat} (htag : s.getMem (claimAddr s k) = eqTag) :
    weightOf s k = some (Model.eqEvalRust (eListAt s (s.getMem (claimAddr s k + 16))
      (s.getMem (claimAddr s k + 24)).toNat) (ptl s)) := by
  have e8 : vecPtr s (claimAddr s k + 8) = s.getMem (claimAddr s k + 16) := by
    show s.getMem (claimAddr s k + 8 + 8) = _; rv_eval []
  have e16 : vecLen s (claimAddr s k + 8) = s.getMem (claimAddr s k + 24) := by
    show s.getMem (claimAddr s k + 8 + 16) = _; rv_eval []
  simp only [weightOf, stackClaimAt, stackWeightAt]
  rw [ite_pos' htag]
  simp only [StackWeightRust.evaluate, vecEs, e8, e16]

theorem evalEq (hEq : FunSpec Image.code 0x8000da88 Proofs.EqEval.Pre Proofs.EqEval.Post)
    {s u : MachineState} {nx WP : Word} {k : Nat} (hpre : BasisPre s)
    (hh : Head s u nx WP k 0x8000d164) (htag : s.getMem (claimAddr s k) = eqTag) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ Got s v nx WP k) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hk := hh.lt
  have hCr := claims_region hpre hk
  have hC := Region.bounds hCr
  have hsp := hh.inv.sp
  have hvs := eq_src hpre hk htag
  have hps := hpre.point
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d164_spec hh.pc (by
    rv_eval [hh.x20]
    simp only [ncl] at hk
    and_intros <;> exact Region.valid hCr (by simp only [claimAddr]; addr_omega [hC, hk])
      (by simp only [claimAddr]; addr_omega [hC, hk]) (by simp only [claimAddr]; addr_omega [hC, hk]))
  have k₁ := b8000d164_keeps h₁
  have hm₁ := b8000d164_mem_same h₁
  have inv₁ := hh.inv.same hm₁ (k₁ .x2 (by decide)) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact k₁ _ (by decide))
  have c16 := Inv.claim hpre hh.inv hk (o := 16) (by decide)
  have c24 := Inv.claim hpre hh.inv hk (o := 24) (by decide)
  rv_eval [] at c16 c24
  have hx10 : t₁.getReg .x10 = s.getReg .x2 - 168 := by rw [b8000d164_x10 h₁, hsp]; rv_eval []
  have hx11 : t₁.getReg .x11 = s.getMem (claimAddr s k + 16) := by
    rw [b8000d164_x11 h₁, hh.x20, c16]
  have hx12 : t₁.getReg .x12 = s.getMem (claimAddr s k + 24) := by
    rw [b8000d164_x12 h₁, hh.x20, c24]
  have hx13 : t₁.getReg .x13 = s.getReg .x12 := by rw [b8000d164_x13 h₁, hh.x19]
  have hx14 : t₁.getReg .x14 = s.getReg .x13 := by rw [b8000d164_x14 h₁, hh.x18]
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₁.sp
  have hsl : stackLo t₁ Proofs.EqEval.stackSize = s.getReg .x2 - 1328 := by
    simp only [stackLo, hsp₁, Proofs.EqEval.stackSize, mulStack, Nat.reduceAdd]; rv_eval []
  have hro := hst.rodata
  have hvsS := hvs.stack
  have hpsS := hps.stack
  have hpreE : Proofs.EqEval.Pre t₁ := {
    ret := by rw [hx10]; valid_sub hst.valid [hb]
    left := by
      rw [hx11, hx12]
      rcases hvs.region with h0 | h0
      · intro i hi; omega
      · have := Region.bounds h0
        exact Region.vrange h0 (Nat.le_refl _) (by omega) this.2.2
    right := by
      rw [hx13, hx14]
      rcases hps.region with h0 | h0
      · intro i hi; omega
      · have := Region.bounds h0
        exact Region.vrange h0 (Nat.le_refl _) (by omega) this.2.2
    stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩
    retStack := by rw [hx10, hsl]; addr_omega [hb]
    leftStack := by rw [hx11, hx12, hsl]; addr_omega [hvsS, hb]
    rightStack := by rw [hx13, hx14, hsl]; addr_omega [hpsS, hb]
    rodata := Inv.rodata' hpre inv₁
    stackRodata := by rw [hsl]; addr_omega [hro, hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hEq.call hr₁ (b8000d164_pc h₁) hpreE
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10, hsl] at hfr₂
  have hnx8 := hst.next
  have inv₂ := Inv.step' hpre inv₁ (DFrame.of_two hfr₂)
    (fun a ha ↦ Or.inr (Or.inl (by
      simp only [basisStack, ringEvalStack, mulStack, stackLo]
      rcases ha with ha | ha <;> addr_omega [ha, hb])))
    (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb])
    ((hfr₂ _ (by addr_omega [hnx8, hb]) (by addr_omega [hnx8, hb])).trans inv₁.next)
    (Nat.le_refl _) inv₁.fits (hpres₂.reg .x2) (hpres₂.reg .x27)
  have hlen := hpost₂.len
  rw [hx12, hx14] at hlen
  have hval := hpost₂.value
  simp only [Proofs.EqEval.left, Proofs.EqEval.right, Proofs.EqEval.len] at hval
  rw [hx10, hx11, hx12, hx13] at hval
  have eL : eListAt t₁ (s.getMem (claimAddr s k + 16)) (s.getMem (claimAddr s k + 24)).toNat =
      eListAt s (s.getMem (claimAddr s k + 16)) (s.getMem (claimAddr s k + 24)).toNat := by
    rw [← Inv.eList hh.inv hvs]; simp only [eListAt, eAt, hm₁]
  have eR : eListAt t₁ (s.getReg .x12) (s.getMem (claimAddr s k + 24)).toNat = ptl s := by
    rw [hlen, ptl, ← Inv.eList hh.inv hps]; simp only [eListAt, eAt, hm₁]
  rw [eL, eR, ← Model.eqEvalRust_eq] at hval
  refine ⟨t₂, hr₂, Or.inr {
    toRegs := hh.toRegs.of_eq fun r hr ↦ by
      rw [hpres₂ r (by unfold calleeSaved; exact Runtime.mem_of_mem hr _), k₁ r (Runtime.mem_of_mem hr _)]
    inv := inv₂
    pc := by rw [hpc₂, returnAddress_eq, b8000d164_x1 h₁]; decide
    lt := hk
    buf := hh.buf
    ws := fun l hl ↦ by
      rw [ws_keep hpre hh.buf hh.inv.fits hk (DFrame.of_two hfr₂) (fun a ha ↦ Or.inl (by
        simp only [basisStack, ringEvalStack, mulStack, stackLo]
        rcases ha with ha | ha <;> addr_omega [ha, hb])) l hl]
      simp only [eAt, hm₁]
      exact hh.ws l hl
    w := by rw [eq_weight htag, hval] }⟩

end Rv64Verifier.Proofs.Pcs.Basis
