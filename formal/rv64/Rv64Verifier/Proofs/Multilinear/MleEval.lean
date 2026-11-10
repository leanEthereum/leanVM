import Rv64Verifier.Proofs.Multilinear.MleEvalHead

/-!
# `multilinear_eval`: the inner loop, the outer loop's tail, the end

`inner_body` takes the inner loop from its head through the product (`mul`, or the table) to
`0x8000d448` (`Pre`); `store` writes `cur[i]` and returns to the head (`IInv`) or, the pass done,
to `0x8000d3a4` (`Done`); `tail` moves to the next coordinate (`OInv`) or to the end (`Last`);
`last` writes `Ok(cur[0])`; `mle_eval_spec` puts them together.
-/

namespace Rv64Verifier.Proofs.Multilinear.MleEval
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F56 Rv64Verifier.Proofs.Multilinear.ScalerFill
  Rv64Verifier.Proofs.Multilinear.EqKernelWin Rv64Verifier.Proofs.Multilinear.MleEvalWin
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The inner loop -/

theorem inner_body (hMul : MulSpec) {s : MachineState} (hpre : MleEvalPre s) (hs : Sized s)
    {P T nx : Word} {k i : Nat} {u : MachineState} (hu : IInv s u P T nx k i) :
    ∃ v, Reaches Image.code u v ∧ (Pre s v P T nx k i ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hk := hu.lt
  have hi := hu.ilt
  obtain ⟨hPN, hn27⟩ := hu.small hs
  simp only [heapEnd] at hPN
  have hsp := hu.inv.sp
  have hPa := hu.align
  have hPlo := hu.lo
  have hlo := hpre.heap.lo
  have htop := hu.top
  have hfit := hu.inv.fits
  have hlen := hs.len
  have hpk : 2 ^ (nn s - k) ≤ 2 ^ nn s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : 2 ^ (nn s - k) = 2 * 2 ^ (nn s - k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hh64 : 2 ^ (nn s - k - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hN : P.toNat + 24 * 2 ^ (nn s - k) ≤ 2 ^ 64 := by omega
  -- `0x8000d478`: the bounds check, never taken
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d478_spec hu.pc (by rv_eval [])
  have k₁ := b8000d478_keeps h₁
  have hm₁ := b8000d478_mem_same h₁
  have hne : u.getReg .x23 ≠ u.getReg .x9 := by rw [hu.x23, hu.x9]; addr_omega [hi, hh64]
  have hx21₁ : u₁.getReg .x21 = P := (k₁ .x21 (by decide)).trans hu.x21
  have hx23₁ : u₁.getReg .x23 = BitVec.ofNat 64 i := (k₁ .x23 (by decide)).trans hu.x23
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 208 := (k₁ .x2 (by decide)).trans hsp
  have haddr : u₁.getReg .x21 + (u₁.getReg .x23 * 32 + u₁.getReg .x23 * 16) =
      P + BitVec.ofNat 64 (24 * (2 * i)) := by
    rw [hx21₁, hx23₁]; addr_omega [hi, hPN, hsplit, hpk]
  have hB : P + BitVec.ofNat 64 (24 * (2 * i + 1)) = P + BitVec.ofNat 64 (24 * (2 * i)) + 24 := by
    addr_omega [hi, hPN, hsplit, hpk]
  -- `0x8000d47c`: `cur[2i]` and the sum
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d47c_spec (b8000d478_pc_not_taken h₁ hne) (by
    rv_eval [hsp₁, haddr]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact heap_valid' (by addr_omega [hPa, hPlo, hlo, hPN, hi, hsplit, hpk])
          (by addr_omega [hPa, hPlo, hlo, hPN, hi, hsplit, hpk])
          (by addr_omega [hPa, hPlo, hlo, hPN, hi, hsplit, hpk]))
  have k₂ := b8000d47c_keeps h₂
  have hm₂ := b8000d47c_frame h₂ (by rw [hsp₁]; addr_omega [hb])
  rw [hsp₁] at hm₂
  rv_eval [] at hm₂
  have hsum : (u₂.getReg .x15, u₂.getReg .x14, u₂.getReg .x11) = Model.limbs
      (eAt u (P + BitVec.ofNat 64 (24 * (2 * i))) + eAt u (P + BitVec.ofNat 64 (24 * (2 * i + 1)))) := by
    rw [limbs_add, limbs_eAt, limbs_eAt, hB, b8000d47c_x15 h₂, b8000d47c_x14 h₂, b8000d47c_x11 h₂,
      haddr]
    simp only [hm₁]
    rv_eval []
    exact Prod.ext (BitVec.xor_comm _ _) (Prod.ext (BitVec.xor_comm _ _) (BitVec.xor_comm _ _))
  have hev : (u₂.getReg .x30, u₂.getReg .x31, u₂.getReg .x8) =
      Model.limbs (eAt u (P + BitVec.ofNat 64 (24 * (2 * i)))) := by
    rw [limbs_eAt, b8000d47c_x30 h₂, b8000d47c_x31 h₂, b8000d47c_x8 h₂, haddr]
    simp only [hm₁]
  have hx25 : u₂.getReg .x25 = BitVec.ofNat 64 (16 * i) := by
    rw [b8000d47c_x25 h₂, hx23₁]; addr_omega [hi, hPN, hsplit, hpk]
  have hmid₁ := hu.toMid.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have mid₂ := hmid₁.step hpre (DwFrame.of_mem hm₂) (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (fun a ha ↦ ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩)
    ((hm₂ _ (by addr_omega [hb, hnx8])).trans hmid₁.inv.next) (Nat.le_refl _) hfit
    fun r hr ↦ k₂ r (mem_of_mem hr _)
  have sc₂ : Sc s u₂ P T nx ((pt s).getD k 0) :=
    Sc.step hpre hu.toMid hu.sc (DwFrame.of_mem fun a ha ↦ (hm₂ a ha).trans (hm₁ a))
      (fun a ha ↦ Or.inr (Or.inl ha)) fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hbuf₂ : eListAt u₂ P (2 ^ (nn s - k)) = eListAt u P (2 ^ (nn s - k)) :=
    (EqKernel.eListAt_frame hm₂ (by addr_omega [hb, hab, hPN, hPlo, hlo, hpk]) hN).trans
      (EqKernel.eListAt_same hm₁ P _)
  have hreg (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x23]) : u₂.getReg r = u.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hm192 : u₂.getMem (s.getReg .x2 - 192) = s.getReg .x13 + BitVec.ofNat 64 (24 * k) := by
    rw [hm₂ _ (by addr_omega [hb]), hm₁]; exact hu.m192
  -- the elements, from any later state whose buffer is `u`'s
  have helem (v : MachineState) (hv : eListAt v P (2 ^ (nn s - k)) = eListAt u P (2 ^ (nn s - k)))
      (j : Nat) (hj : j < 2 ^ (nn s - k)) :
      eAt v (P + BitVec.ofNat 64 (24 * j)) = eAt u (P + BitVec.ofNat 64 (24 * j)) := by
    rw [← EqKernel.eListAt_getD' v P hj, hv, EqKernel.eListAt_getD' u P hj]
  by_cases htag : u.getReg .x28 = 0
  · -- the table
    obtain ⟨h27, hBuf, hPT, hTt, htab⟩ := hu.sc.table htag
    have hTh := hBuf.hi
    obtain ⟨v, hr₃, hpc₃, hk₃, hm₃, hprod⟩ := table_mul hBuf
      (b8000d47c_pc_not_taken h₂ (by rw [k₁ .x28 (by decide)]; exact htag))
      (by rw [k₂ .x26 (by decide), k₁ .x26 (by decide), hu.sc.x26])
      (by rw [k₂ .x27 (by decide), k₁ .x27 (by decide), h27])
      (by rw [k₂ .x20 (by decide), k₁ .x20 (by decide), hu.x20])
      (by rw [k₂ .x22 (by decide), k₁ .x22 (by decide), hu.x22])
      (by rw [k₂ .x24 (by decide), k₁ .x24 (by decide), hu.x24])
    have htab₂ : tab u₂ T = tab u T :=
      EqKernel.tab_dw (DwFrame.of_mem fun a ha ↦ (hm₂ a ha).trans (hm₁ a))
        (fun a ha hx ↦ by addr_omega [ha, hx, hb, hab, hTh])
        (by simp only [tabBytes, heapEnd] at hTh ⊢; omega)
    rw [hsum, htab₂, htab, Model.scaledMul_eq, mul_comm] at hprod
    have hbufv : eListAt v P (2 ^ (nn s - k)) = eListAt u P (2 ^ (nn s - k)) :=
      (EqKernel.eListAt_same hm₃ P _).trans hbuf₂
    have hj0 : 2 * i < 2 ^ (nn s - k) := by omega
    have hj1 : 2 * i + 1 < 2 ^ (nn s - k) := by omega
    refine ⟨v, hr₁.trans (hr₂.trans hr₃), Or.inl {
      toMid := mid₂.same hpre hm₃ fun r hr ↦ hk₃ r (mem_of_mem hr _)
      pc := hpc₃
      lt := hk
      ilt := hi
      m192 := (hm₃ _).trans hm192
      x19 := by rw [hk₃ _ (by decide), hreg _ (by decide), hu.x19]
      x9 := by rw [hk₃ _ (by decide), hreg _ (by decide), hu.x9]
      x23 := by rw [hk₃ _ (by decide), hreg _ (by decide), hu.x23]
      x25 := (hk₃ _ (by decide)).trans hx25
      sc := Sc.step hpre mid₂ sc₂ (DwFrame.same hm₃ fun _ ↦ False) (fun _ h ↦ h.elim)
        fun r hr ↦ hk₃ r (mem_of_mem hr _)
      buf := hbufv.trans hu.buf
      even := by
        rw [hk₃ _ (by decide), hk₃ _ (by decide), hk₃ _ (by decide), hev, helem v hbufv _ hj0]
      prod := by rw [hprod, helem v hbufv _ hj0, helem v hbufv _ hj1] }⟩
  · -- `mul`
    obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d3f0_spec
      (b8000d47c_pc_taken h₂ (by rw [k₁ .x28 (by decide)]; exact htag)) (by rv_eval [])
    have k₃ := b8000d3f0_keeps h₃
    have hm₃ := b8000d3f0_mem_same h₃
    have hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 208 := (k₂ .x2 (by decide)).trans hsp₁
    have hsp₃ : u₃.getReg .x2 = s.getReg .x2 - 208 := (k₃ .x2 (by decide)).trans hsp₂
    have hx10 : u₃.getReg .x10 = s.getReg .x2 - 184 := by rw [b8000d3f0_x10 h₃, hsp₂]; rv_eval []
    have hx11 : u₃.getReg .x11 = s.getReg .x2 - 128 := by rw [b8000d3f0_x11 h₃, hsp₂]; rv_eval []
    have hx12 : u₃.getReg .x12 = s.getReg .x2 - 152 := by rw [b8000d3f0_x12 h₃, hsp₂]; rv_eval []
    have hsl : stackLo u₃ mulStack = s.getReg .x2 - 1232 := by
      simp only [stackLo, mulStack, hsp₃, Sym.sub_sub_lit]; rfl
    have res₃ := mid₂.toRes.same hpre hm₃ (k₃ .x2 (by decide))
    have hpre₃ : MulPre u₃ := {
      out := by rw [hx10]; valid_sub hst.valid [hb]
      lhs := by rw [hx11]; valid_sub hst.valid [hb]
      rhs := by rw [hx12]; valid_sub hst.valid [hb]
      stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₃]; addr_omega [hb]⟩
      outLhs := by rw [hx10, hx11]; addr_omega [hb]
      outRhs := by rw [hx10, hx12]; addr_omega [hb]
      outStack := by rw [hx10, hsl]; addr_omega [hb]
      lhsStack := by rw [hx11, hsl]; addr_omega [hb]
      rhsStack := by rw [hx12, hsl]; addr_omega [hb]
      rodata := res₃.inv.rodataOk hpre
      stackRodata := by rw [hsl]; addr_omega [hb, hst.rodata] }
    obtain ⟨w, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hdead⟩ := hMul.call hr₃ (b8000d3f0_pc h₃) hpre₃
    swap
    · exact ⟨w, hr₁.trans (hr₂.trans hr₄), Or.inr hdead⟩
    have hdw := MulPost.dwFrame hpost₄
    rw [hx10, hsl] at hdw
    have hval := hpost₄.value
    rw [hx10, hx11, hx12] at hval
    have hsp₄ : w.getReg .x2 = s.getReg .x2 - 208 := (hpres₄.reg .x2).trans hsp₃
    obtain ⟨v, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000d41c_spec
      (by rw [hpc₄, returnAddress_eq, b8000d3f0_x1 h₃]; decide) (by
        rv_eval [hsp₄]; and_intros <;> valid_access hst.valid [hb])
    have k₅ := b8000d41c_keeps h₅
    have hm₅ := b8000d41c_mem_same h₅
    have hdwv : DwFrame u₂ v fun a ↦ Within a (s.getReg .x2 - 184) 24 ∨
        Within a (s.getReg .x2 - 1232) mulStack := fun a h1 h2 ↦
      (hm₅ a).trans ((hdw a h1 h2).trans (hm₃ a))
    have hX (a : Word) (ha : Within a (s.getReg .x2 - 184) 24 ∨
        Within a (s.getReg .x2 - 1232) mulStack) : Within a (s.getReg .x2 - 1232) 1072 := by
      rcases ha with ha | ha <;> addr_omega [ha, hb]
    have hpr (r : Reg) (hr : r ∈ calleeSaved := by decide) : w.getReg r = u₃.getReg r := hpres₄ r hr
    have hnxw : v.getMem nextAddr = nx := by
      rw [EqKernel.DwFrame.keep hdwv fun i hi hx ↦ by
        rcases hx with hx | hx <;> addr_omega [hx, hi, hb, hnx8]]
      exact mid₂.inv.next
    have mid₅ : Mid s v P nx := mid₂.step hpre hdwv
      (fun a ha ↦ Or.inl (by have := hX a ha; addr_omega [this, hb]))
      (fun a ha ↦ by
        rcases ha with ha | ha
        · exact ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩
        · exact ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩)
      hnxw (Nat.le_refl _) hfit fun r hr ↦ by
        simp only [midRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [k₅ .x2 (by decide), hpr .x2, k₃ .x2 (by decide)]
        · rw [b8000d41c_x20 h₅, mid₂.x20]
        · rw [b8000d41c_x21 h₅, hpr .x18, b8000d3f0_x18 h₃]
        · rw [b8000d41c_x22 h₅, mid₂.x22]
        · rw [k₅ .x24 (by decide), hpr .x24, k₃ .x24 (by decide)]
    have hbufv : eListAt v P (2 ^ (nn s - k)) = eListAt u P (2 ^ (nn s - k)) := by
      rw [EqKernel.eListAt_dw hdwv (fun a ha hx ↦ by
          have := hX _ hx; addr_omega [this, ha, hb, hab, hPN, hpk]) hN, hbuf₂]
    have hj0 : 2 * i < 2 ^ (nn s - k) := by omega
    have hj1 : 2 * i + 1 < 2 ^ (nn s - k) := by omega
    have hr_eq : eAt u₃ (s.getReg .x2 - 152) = (pt s).getD k 0 := by
      rw [← sc₂.plain (by rw [k₂ .x28 (by decide), k₁ .x28 (by decide)]; exact htag)]
      unfold eAt
      rw [hm₃, hm₃, hm₃]
    have hsum₃ : eAt u₃ (s.getReg .x2 - 128) = eAt u (P + BitVec.ofNat 64 (24 * (2 * i))) +
        eAt u (P + BitVec.ofNat 64 (24 * (2 * i + 1))) := by
      apply eAt_eq_of_limbs
      have m80 := b8000d47c_m_x2_80 h₂
      have m88 := b8000d47c_m_x2_88 h₂
      have m96 := b8000d47c_m_x2_96 h₂
      rw [hsp₁, ← b8000d47c_x15 h₂] at m80
      rw [hsp₁, ← b8000d47c_x14 h₂] at m88
      rw [hsp₁, ← b8000d47c_x11 h₂] at m96
      rv_eval [] at m80 m88 m96
      rw [hm₃, hm₃, hm₃]
      rv_eval [m80, m88, m96]
      exact hsum
    refine ⟨v, hr₁.trans (hr₂.trans (hr₄.trans hr₅)), Or.inl {
      toMid := mid₅
      pc := b8000d41c_pc h₅
      lt := hk
      ilt := hi
      m192 := by
        rw [hm₅, EqKernel.DwFrame.keep hdw fun i hi hx ↦ by
          rcases hx with hx | hx <;> addr_omega [hx, hi, hb], hm₃]
        exact hm192
      x19 := by
        rw [b8000d41c_x19 h₅, hpr .x21, b8000d3f0_x21 h₃, hreg _ (by decide), hu.x19]
      x9 := by rw [k₅ .x9 (by decide), hpr .x9, k₃ .x9 (by decide), hreg _ (by decide), hu.x9]
      x23 := by
        rw [k₅ .x23 (by decide), hpr .x23, k₃ .x23 (by decide), hreg _ (by decide), hu.x23]
      x25 := by rw [k₅ .x25 (by decide), hpr .x25, k₃ .x25 (by decide), hx25]
      sc := Sc.step hpre mid₂ sc₂ hdwv (fun a ha ↦ Or.inl (hX a ha)) fun r hr ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [k₅ .x26 (by decide), hpr .x26, k₃ .x26 (by decide)]
        · rw [k₅ .x27 (by decide), hpr .x27, k₃ .x27 (by decide)]
        · rw [b8000d41c_x28 h₅, hpr .x19, b8000d3f0_x19 h₃]
      buf := hbufv.trans hu.buf
      even := by
        rw [b8000d41c_x30 h₅, b8000d41c_x31 h₅, b8000d41c_x8 h₅, hpr .x8, hpr .x20, hpr .x22,
          b8000d3f0_x8 h₃, b8000d3f0_x20 h₃, b8000d3f0_x22 h₃, hev, helem v hbufv _ hj0]
      prod := by
        rw [b8000d41c_x10 h₅, b8000d41c_x12 h₅, b8000d41c_x13 h₅, hsp₄,
          helem v hbufv _ hj0, helem v hbufv _ hj1, ← hsum₃, ← hr_eq, ← hval, limbs_eAt]
        rv_eval [] }⟩

theorem store {s : MachineState} (hpre : MleEvalPre s) (hs : Sized s) {P T nx : Word} {k i : Nat}
    {u : MachineState} (hu : Pre s u P T nx k i) :
    ∃ v, Reaches Image.code u v ∧ (IInv s v P T nx k (i + 1) ∨ Done s v P nx k) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hk := hu.lt
  have hi := hu.ilt
  obtain ⟨hPN, hn27⟩ := hu.small hs
  simp only [heapEnd] at hPN
  have hPa := hu.align
  have hPlo := hu.lo
  have hlo := hpre.heap.lo
  have htop := hu.top
  have hfit := hu.inv.fits
  have hlen := hs.len
  have hpk : 2 ^ (nn s - k) ≤ 2 ^ nn s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : 2 ^ (nn s - k) = 2 * 2 ^ (nn s - k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hh64 : 2 ^ (nn s - k - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hN : P.toNat + 24 * 2 ^ (nn s - k) ≤ 2 ^ 64 := by omega
  have haddr : u.getReg .x21 + (u.getReg .x25 + u.getReg .x23 * 8) =
      P + BitVec.ofNat 64 (24 * i) := by
    rw [hu.x21, hu.x25, hu.x23]; addr_omega [hi, hPN, hsplit, hpk]
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000d448_spec hu.pc (by
    rv_eval [haddr]
    and_intros <;> exact heap_valid' (by addr_omega [hPa, hPlo, hlo, hPN, hi, hsplit, hpk])
      (by addr_omega [hPa, hPlo, hlo, hPN, hi, hsplit, hpk])
      (by addr_omega [hPa, hPlo, hlo, hPN, hi, hsplit, hpk]))
  have k₁ := b8000d448_keeps h
  have hfr : ∀ a, ¬ Within a (P + BitVec.ofNat 64 (24 * i)) 24 → v.getMem a = u.getMem a := by
    intro a ha
    refine h.frame a ?_
    rv_eval [haddr]
    and_intros <;> intro heq <;> apply ha <;> rw [heq] <;> addr_omega [hPN, hi, hsplit, hpk]
  have hnew : eAt v (P + BitVec.ofNat 64 (24 * i)) = eAt u (P + BitVec.ofNat 64 (24 * (2 * i))) +
      (eAt u (P + BitVec.ofNat 64 (24 * (2 * i))) +
        eAt u (P + BitVec.ofNat 64 (24 * (2 * i + 1)))) * (pt s).getD k 0 := by
    apply eAt_eq_of_limbs
    have m0 := b8000d448_m0 h
    have m1 := b8000d448_m1 h
    have m2 := b8000d448_m2 h
    rw [haddr] at m0 m1 m2
    rw [m2, m1, m0, limbs_add, ← hu.even, ← hu.prod]
    exact Prod.ext (BitVec.xor_comm _ _) (Prod.ext (BitVec.xor_comm _ _) (BitVec.xor_comm _ _))
  have hj0 : 2 * i < 2 ^ (nn s - k) := by omega
  have hj1 : 2 * i + 1 < 2 ^ (nn s - k) := by omega
  have hbuf : eListAt v P (2 ^ (nn s - k)) =
      (List.range (i + 1)).foldl (Model.mleStep ((pt s).getD k 0)) (cur s k) := by
    rw [EqKernel.eListAt_set1 (by omega) hN hfr, hnew, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil, ← hu.buf]
    simp only [Model.mleStep]
    rw [EqKernel.eListAt_getD' _ _ hj0, EqKernel.eListAt_getD' _ _ hj1]
  have hX (a : Word) (ha : Within a (P + BitVec.ofNat 64 (24 * i)) 24) : Within a P (24 * ll s) := by
    addr_omega [ha, hPN, hi, hsplit, hpk, hlen]
  have mid := hu.toMid.step hpre (DwFrame.of_mem hfr)
    (fun a ha ↦ Or.inr (Or.inr ⟨by have := hX a ha; addr_omega [this, hPlo],
      by have := hX a ha; addr_omega [this, htop]⟩))
    (fun a ha ↦ by
      have := hX a ha
      exact ⟨by addr_omega [this, hb, hab, htop, hfit], by addr_omega [this, hb, hab, htop, hfit]⟩)
    ((hfr _ (by addr_omega [hPN, hi, hsplit, hpk])).trans hu.inv.next) (Nat.le_refl _) hfit
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  have sc := Sc.step hpre hu.toMid hu.sc (DwFrame.of_mem hfr) (fun a ha ↦ Or.inr (Or.inr (hX a ha)))
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  have m192 : v.getMem (s.getReg .x2 - 192) = s.getReg .x13 + BitVec.ofNat 64 (24 * k) :=
    (hfr _ (by addr_omega [hb, hab, hPN, hi, hsplit, hpk])).trans hu.m192
  by_cases hlast : i + 1 = 2 ^ (nn s - k - 1)
  · refine ⟨v, hr, Or.inr {
      toMid := mid
      pc := b8000d448_pc_taken h (by rw [hu.x23, hu.x19]; addr_omega [hlast, hh64])
      lt := hk
      m192 := m192
      x19 := (k₁ .x19 (by decide)).trans hu.x19
      buf := pass_done hs hk (by rw [hbuf, hlast]) }⟩
  · refine ⟨v, hr, Or.inl {
      toMid := mid
      pc := b8000d448_pc_not_taken h (by rw [hu.x23, hu.x19]; addr_omega [hlast, hi, hh64])
      lt := hk
      ilt := by omega
      m192 := m192
      x19 := (k₁ .x19 (by decide)).trans hu.x19
      x9 := (k₁ .x9 (by decide)).trans hu.x9
      x23 := by rw [b8000d448_x23 h, hu.x23]; addr_omega [hi, hh64]
      sc := sc
      buf := hbuf }⟩

theorem inner_loop (hMul : MulSpec) {s : MachineState} (hpre : MleEvalPre s) (hs : Sized s)
    {P T nx : Word} {k : Nat} {u : MachineState} (hu : IInv s u P T nx k 0) :
    ∃ v, Reaches Image.code u v ∧ (Done s v P nx k ∨ Dead Image.code v) := by
  refine Reaches.loop (code := Image.code) (fun v ↦ ∃ i, IInv s v P T nx k i)
    (fun v ↦ 2 ^ (nn s - k - 1) - (v.getReg .x23).toNat) _ (fun v ⟨i, hv⟩ ↦ ?_) u ⟨0, hu⟩
  have hi := hv.ilt
  have hk := hv.lt
  have h64 := hs.lt
  have hh64 : 2 ^ (nn s - k - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨w, hr, hw | hd⟩ := inner_body hMul hpre hs hv
  · obtain ⟨x, hr', hx | hx⟩ := store hpre hs hw
    · refine Or.inr ⟨x, hr.trans hr', ⟨i + 1, hx⟩, ?_⟩
      rw [hx.x23, hv.x23, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      have := hx.ilt
      omega
    · exact Or.inl ⟨x, hr.trans hr', Or.inl hx⟩
  · exact Or.inl ⟨w, hr, Or.inr hd⟩

/-! ## The outer loop's tail -/

theorem tail {s : MachineState} (hpre : MleEvalPre s) {P nx : Word} {k : Nat}
    {u : MachineState} (hu : Done s u P nx k) :
    ∃ v, Reaches Image.code u v ∧ (OInv s v P nx (k + 1) ∨ Last s v P nx) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hk := hu.lt
  have hsp := hu.inv.sp
  have hpb := ValidMemRange.bounds (pointValid hpre (by omega)) (by omega)
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000d3a4_spec hu.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000d3a4_keeps h
  have hm := b8000d3a4_mem_same h
  have mid := hu.toMid.same hpre hm fun r hr ↦ k₁ r (mem_of_mem hr _)
  have e16 : u.getMem (u.getReg .x2 + 16) = s.getReg .x13 + BitVec.ofNat 64 (24 * k) := by
    rw [hsp]; rv_eval [hu.m192]
  have e8 : u.getMem (u.getReg .x2 + 8) = s.getReg .x13 + BitVec.ofNat 64 (24 * nn s) := by
    rw [hsp]; rv_eval [hu.stop]
  have hbuf := (EqKernel.eListAt_same hm P _).trans hu.buf
  by_cases hlast : k + 1 = nn s
  · refine ⟨v, hr, Or.inr {
      toRes := mid.toRes
      pc := b8000d3a4_pc_taken h (by rw [e16, e8]; addr_omega [hpb, hlast])
      x19 := ?_
      x21 := (k₁ .x21 (by decide)).trans hu.x21
      val := ?_ }⟩
    · rw [k₁ .x19 (by decide), hu.x19, show nn s - k - 1 = 0 by omega]
      decide
    · rw [← hlast, ← hbuf, show nn s - (k + 1) = 0 by omega, EqKernel.eListAt_getD' _ _ (by norm_num)]
      simp
  · refine ⟨v, hr, Or.inl {
      toMid := mid
      pc := b8000d3a4_pc_not_taken h (by rw [e16, e8]; addr_omega [hpb, hlast, hk])
      lt := by omega
      x11 := by rw [b8000d3a4_x11 h, e16]; addr_omega [hpb, hk]
      x8 := by rw [b8000d3a4_x8 h, hu.x19, show nn s - k - 1 = nn s - (k + 1) by omega]
      buf := hbuf }⟩

/-! ## The end -/

theorem last {s : MachineState} (hpre : MleEvalPre s) (hs : Sized s) {P nx : Word}
    {u : MachineState} (hu : Last s u P nx) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ MleEvalPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hsp := hu.inv.sp
  obtain ⟨hPN, -⟩ := hu.small hs
  simp only [heapEnd] at hPN
  have hPa := hu.align
  have hPlo := hu.lo
  have hlo := hpre.heap.lo
  have hpos : 0 < 2 ^ nn s := Nat.two_pow_pos _
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d5c0_spec hu.pc (by rv_eval [])
  have k₁ := b8000d5c0_keeps h₁
  have hm₁ := b8000d5c0_mem_same h₁
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 208 := (k₁ .x2 (by decide)).trans hsp
  have hx21₁ : u₁.getReg .x21 = P := (k₁ .x21 (by decide)).trans hu.x21
  have hout₁ : u₁.getMem (s.getReg .x2 - 208) = s.getReg .x10 := (hm₁ _).trans hu.outp
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d5c4_spec
    (b8000d5c0_pc_not_taken h₁ hu.x19) (by
      rv_eval [hsp₁, hout₁, hx21₁]
      and_intros <;> first
        | valid_access (outValid hpre) [hb]
        | valid_access hst.valid [hb]
        | exact heap_valid' (by addr_omega [hPa, hPlo, hlo, hPN, hpos])
            (by addr_omega [hPa, hPlo, hlo, hPN, hpos]) (by addr_omega [hPa, hPlo, hlo, hPN, hpos]))
  have k₂ := b8000d5c4_keeps h₂
  have hfr₂ : ∀ a, ¬ Within a (s.getReg .x10 + 8) 24 → u₂.getMem a = u₁.getMem a := by
    intro a ha
    refine h₂.frame a ?_
    rv_eval [hsp₁, hout₁]
    and_intros <;> intro heq <;> apply ha <;> rw [heq] <;> addr_omega [hb]
  have inv₁ := hu.inv.same hpre hm₁ (k₁ .x2 (by decide))
  have inv₂ := inv₁.step hpre (DwFrame.of_mem hfr₂) (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (fun a ha ↦ by addr_omega [ha, hb, hos]) ((hfr₂ _ (by addr_omega [hb, hof.2])).trans inv₁.next)
    (Nat.le_refl _) inv₁.fits (k₂ .x2 (by decide))
  have m0 := b8000d5c4_m0 h₂
  have m1 := b8000d5c4_m1 h₂
  have m2 := b8000d5c4_m2 h₂
  rw [hsp₁, hout₁, hx21₁] at m0 m1 m2
  have hval : eAt u₂ (s.getReg .x10 + 8) = eAt u P :=
    eAt_congr (by rw [m2, hm₁]) (by rv_eval [m1, hm₁]) (by rv_eval [m0, hm₁])
  obtain ⟨t, hr, ht⟩ := finish hpre inv₂ (b8000d5c4_pc h₂) (by rw [b8000d5c4_x8 h₂, hsp₁, hout₁])
    (by
      rw [value_eq hs]
      exact ⟨b8000d5c4_x12 h₂, hval.trans hu.val⟩)
  exact ⟨t, hr₁.trans (hr₂.trans hr), Or.inl ht⟩

/-! ## `multilinear_eval` -/

/-- **`multilinear_eval` meets its contract**, given `try_allocate_in`'s, `reserve`'s (room enough),
`memcpy`'s, `Scaler::new`'s and `mul`'s. -/
theorem mle_eval_spec (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x80008a10)
    (hC : MemcpySpec 0x800126e4) (hS : ScalerSpec) (hMul : MulSpec) : MleEvalSpec := by
  intro s hpc hpre
  by_cases hs : Sized s
  swap
  · obtain ⟨t, hr, ht⟩ := err hpc hpre hs
    exact ⟨t, hr, Or.inl ht⟩
  have h64 := hs.lt
  obtain ⟨u, hr, ⟨P, nx, hu⟩ | ⟨P, nx, hu⟩ | hd⟩ := prologue hT hR hC hpc hpre hs
  · obtain ⟨v, hr', hv⟩ := Reaches.loop (code := Image.code) (fun v ↦ ∃ nx k, OInv s v P nx k)
      (fun v ↦ (v.getReg .x8).toNat)
      (fun v ↦ (∃ nx, Last s v P nx) ∨ Dead Image.code v) (fun v ⟨nx, k, hv⟩ ↦ by
        have hk := hv.lt
        obtain ⟨w, hr₁, ⟨T, nx', hw⟩ | hd⟩ := outer_head hS hpre hs hv
        · obtain ⟨x, hr₂, hx | hd⟩ := inner_loop hMul hpre hs hw
          · obtain ⟨y, hr₃, hy | hy⟩ := tail hpre hx
            · refine Or.inr ⟨y, hr₁.trans (hr₂.trans hr₃), ⟨nx', k + 1, hy⟩, ?_⟩
              have h1 : 2 ^ (nn s - k) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
              have h2 : 2 ^ (nn s - (k + 1)) < 2 ^ (nn s - k) :=
                Nat.pow_lt_pow_right (by norm_num) (by omega)
              rw [hy.x8, hv.x8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
                Nat.mod_eq_of_lt (by omega)]
              exact h2
            · exact Or.inl ⟨y, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨nx', hy⟩⟩
          · exact Or.inl ⟨x, hr₁.trans hr₂, Or.inr hd⟩
        · exact Or.inl ⟨w, hr₁, Or.inr hd⟩) u ⟨nx, 0, hu⟩
    rcases hv with ⟨nx', he⟩ | hd
    · obtain ⟨t, hr'', ht⟩ := last hpre hs he
      exact ⟨t, hr.trans (hr'.trans hr''), ht⟩
    · exact ⟨v, hr.trans hr', Or.inr hd⟩
  · obtain ⟨t, hr', ht⟩ := last hpre hs hu
    exact ⟨t, hr.trans hr', ht⟩
  · exact ⟨u, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Multilinear.MleEval
