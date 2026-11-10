import Rv64Verifier.Proofs.Pcs.RingSwitchImg

/-!
# `ring_switch`: a stage of the images loop

`0x80009a90` counts down, `0x80009a98` copies the value to `F + 176` and calls
`pow(F + 336, F + 176, 1 << shift)`, `0x80009ac4` calls `mul(F + 176, challenge, F + 336)`,
`0x80009ad8` adds the product to the value and moves on.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section
variable {s B2 u : MachineState} {C chP I nx : Word} {ch : List E}

theorem rodataU2 (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch) (h : Ph B2 u (w2 s I) nx) :
    RodataOk u := by
  have hb := bounds hpre
  have hTr := hpre.self.rodata
  have hH := hctx.heap.hi
  have hI := hctx.iR
  have hP := Region.bounds hpre.self.ok.self
  simp only [transcriptSize] at hP
  have hro : RodataOk B2 := hpre.rodata.dframe hctx.frame fun a ha hW ↦ by
    rcases hW with (hW | hW | hW) | hW
    · addr_omega [ha, hW, hTr, hP]
    · addr_omega [ha, hW, hb]
    · addr_omega [ha, hW]
    · simp only [Fresh] at hW; addr_omega [ha, hW.2, hH]
  refine h.rodata hro (fun a ha hr ↦ ?_) (by simp only [stackLo, hctx.sp]; addr_omega [hb])
  rcases ha with ha | ha
  · addr_omega [ha, hr, hb]
  · simp only [nS] at hI ha
    rcases hI with hI | hI
    · simp only [hI] at ha; addr_omega [ha]
    · addr_omega [ha, hr, hI.2, hH]

theorem iStage (hP : PowSpec) (hM : MulSpec) (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch)
    {i j : Nat} (hc : IStage s B2 u chP I ch nx i j) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨
      (j + 1 < 6 ∧ IStage s B2 v chP I ch nx i (j + 1)) ∨ (j + 1 = 6 ∧ IPush s B2 v I ch nx i)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := hc.ph.sp.trans hctx.sp
  have hj := hc.ltj
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  have hcC := hctx.chC
  have hcA := hctx.chA
  have hcL := hctx.chLo
  have hlo := hpre.heap.lo
  simp only [heapStart] at hlo
  have hchV : ValidMemRange chP 18 :=
    MultilinearWords.heap_valid_range hcA (by simp only [heapStart]; omega)
      (by simp only [heapEnd] at hH ⊢; omega)
  have hl := hctx.chLen
  have hI := hctx.iR
  simp only [nS] at hI
  -- the count down
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009a90_spec hc.pc trivial
  have k₁ := b80009a90_keeps h₁
  have hm₁ := b80009a90_mem_same h₁
  have hpc₁ := b80009a90_pc_not_taken h₁ (by rw [hc.x20]; addr_omega [hj])
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 192 + BitVec.ofNat 64 (8 * j) :=
    (k₁ .x10 (by decide)).trans hc.x10
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 464 := (k₁ .x2 (by decide)).trans hsp
  -- the value to `F + 176`, `pow`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009a98_spec hpc₁ (by
    rv_eval [hsp₁, hx10₁]
    and_intros <;> valid_access hst.valid [hj, hb])
  have k₂ := b80009a98_keeps h₂
  have hm₂ := b80009a98_frame h₂ (by rw [hsp₁]; addr_omega [hb])
  rw [hsp₁] at hm₂
  rv_eval [] at hm₂
  have hsh : t₁.getMem (t₁.getReg .x10) = shiftW j := by
    rw [hx10₁, hm₁]; exact hc.shifts j hj
  have hx12₂ : t₂.getReg .x12 = t₁.getReg .x9 <<< ((t₁.getMem (t₁.getReg .x10)).toNat % 64) :=
    h₂.reg_eq .x12 rfl (by rv_eval [])
  have hexp : (t₂.getReg .x12).toNat = 2 ^ ringMapShiftsRust.getD j 0 := by
    have hp := shift_pos j hj
    rw [hx12₂, hsh, k₁ .x9 (by decide), hc.x9, shift_toNat j hj]
    exact one_shl _ (by omega)
  have w0 := b80009a98_m_x2_176 h₂
  have w1' := b80009a98_m_x2_184 h₂
  have w2' := b80009a98_m_x2_192 h₂
  rw [hsp₁] at w0 w1' w2'
  rv_eval [k₁ .x25 (by decide), k₁ .x8 (by decide), k₁ .x18 (by decide)] at w0 w1' w2'
  have hval := hc.val
  have eV : eAt t₂ (s.getReg .x2 - 288) = img ch (sv s i) j := by
    apply eAt_eq_of_limbs
    rw [hval]; rv_eval [w0, w1', w2']
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 464 := (k₂ .x2 (by decide)).trans hsp₁
  have hx10₂ : t₂.getReg .x10 = s.getReg .x2 - 128 := by rw [b80009a98_x10 h₂, hsp₁]; rv_eval []
  have hx11₂ : t₂.getReg .x11 = s.getReg .x2 - 288 := by rw [b80009a98_x11 h₂, hsp₁]; rv_eval []
  have hsl₂ : stackLo t₂ powStack = s.getReg .x2 - 1568 := by
    simp only [stackLo, powStack, mulStack, hsp₂, Nat.reduceAdd]; rv_eval []
  have ph₂ := (hc.ph.same hm₁ (k₁ .x2 (by decide))).step (DFrame.of_memFrame hm₂)
    (fun a ha ↦ Or.inl (Or.inl (by addr_omega [ha, hb])))
    ((hm₂ _ (by addr_omega [hb])).trans ((hm₁ _).trans hc.ph.next)) (Nat.le_refl _) hc.ph.fits
    (k₂ .x2 (by decide))
  obtain ⟨t₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hP.call hr₂ (b80009a98_pc h₂) {
    out := by rw [hx10₂]; valid_sub hst.valid [hb]
    base := by rw [hx11₂]; valid_sub hst.valid [hb]
    stack := (hst.sub 464 hsp₂ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    pool := poolOk_of_rodata (rodataU2 hpre hctx ph₂)
      (by rw [hsl₂]; simp only [powStack, mulStack]; addr_omega [hb])
    outBase := by rw [hx10₂, hx11₂]; addr_omega [hb]
    outStack := by rw [hx10₂, hsl₂]; simp only [powStack, mulStack]; addr_omega [hb]
    baseStack := by rw [hx11₂, hsl₂]; simp only [powStack, mulStack]; addr_omega [hb]
    basePool := by rw [hx11₂]; addr_omega [hb] }
  swap
  · exact ⟨t₃, hr₁.trans hr₃, Or.inl hd⟩
  have hv₃ := hpost₃.value
  rw [hx10₂, hx11₂, hexp, eV] at hv₃
  have hf₃ := hpost₃.frame
  rw [hx10₂, hx11₂, hsl₂] at hf₃
  simp only [powStack, mulStack, Nat.reduceAdd] at hf₃
  have hD₃ := dframe_of_three hf₃
  have ph₃ := ph₂.step hD₃
    (fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by simp only [stackLo, hctx.sp]; addr_omega [ha, hb])))
    ((hf₃ _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])).trans ph₂.next)
    (Nat.le_refl _) ph₂.fits (hpres₃.reg .x2)
  -- `mul`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009ac4_spec
    (by rw [hpc₃, returnAddress_eq, b80009a98_x1 h₂]; decide) trivial
  have k₄ := b80009ac4_keeps h₄
  have hm₄ := b80009ac4_mem_same h₄
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 464 := (hpres₃.reg .x2).trans hsp₂
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 464 := (k₄ .x2 (by decide)).trans hsp₃
  have hx22₃ : t₃.getReg .x22 = chP + BitVec.ofNat 64 (24 * j) := by
    rw [hpres₃.reg .x22, k₂ .x22 (by decide), k₁ .x22 (by decide), hc.x22]
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 288 := by rw [b80009ac4_x10 h₄, hsp₃]; rv_eval []
  have hx11₄ : t₄.getReg .x11 = chP + BitVec.ofNat 64 (24 * j) := by rw [b80009ac4_x11 h₄, hx22₃]
  have hx12₄ : t₄.getReg .x12 = s.getReg .x2 - 128 := by rw [b80009ac4_x12 h₄, hsp₃]; rv_eval []
  have hsl₄ : stackLo t₄ mulStack = s.getReg .x2 - 1488 := by
    simp only [stackLo, mulStack, hsp₄]; rv_eval []
  have ph₄ := ph₃.same hm₄ (k₄ .x2 (by decide))
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hd⟩ := hM.call hr₄ (b80009ac4_pc h₄) {
    out := by rw [hx10₄]; valid_sub hst.valid [hb]
    lhs := by rw [hx11₄]; valid_sub hchV [hj, hcC, hC, hH, hcA]
    rhs := by rw [hx12₄]; valid_sub hst.valid [hb]
    stack := (hst.sub 464 hsp₄ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    outLhs := by rw [hx10₄, hx11₄]; addr_omega [hj, hcC, hC, hH, hb]
    outRhs := by rw [hx10₄, hx12₄]; addr_omega [hb]
    outStack := by rw [hx10₄, hsl₄]; simp only [mulStack]; addr_omega [hb]
    lhsStack := by rw [hx11₄, hsl₄]; simp only [mulStack]; addr_omega [hj, hcC, hC, hH, hb]
    rhsStack := by rw [hx12₄, hsl₄]; simp only [mulStack]; addr_omega [hb]
    rodata := rodataU2 hpre hctx ph₄
    stackRodata := by rw [hsl₄]; simp only [mulStack]; addr_omega [hb] }
  swap
  · exact ⟨t₅, hr₁.trans (hr₃.trans hr₅), Or.inl hd⟩
  have hv₅ := hpost₅.value
  rw [hx10₄, hx11₄, hx12₄, keepCh2 hpre hctx ph₄ hj] at hv₅
  have hp₄ : eAt t₄ (s.getReg .x2 - 128) = img ch (sv s i) j ^ 2 ^ ringMapShiftsRust.getD j 0 := by
    rw [← hv₃]; simp only [eAt, hm₄]
  rw [hp₄] at hv₅
  have hf₅ := hpost₅.frame
  rw [hx10₄, hsl₄] at hf₅
  simp only [mulStack] at hf₅
  have hD₅ := dframe_of_two hf₅
  have ph₅ := ph₄.step hD₅
    (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by simp only [stackLo, hctx.sp]; addr_omega [ha, hb])))
    ((hf₅ _ (by addr_omega [hb]) (by addr_omega [hb])).trans ph₄.next)
    (Nat.le_refl _) ph₄.fits (hpres₅.reg .x2)
  -- the sum, and on
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80009ad8_spec
    (by rw [hpc₅, returnAddress_eq, b80009ac4_x1 h₄]; decide) (by
      rv_eval [hpres₅.reg .x2, hsp₄]
      and_intros <;> valid_access hst.valid [hb])
  have k₆ := b80009ad8_keeps h₆
  have hm₆ := b80009ad8_mem_same h₆
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 464 := (hpres₅.reg .x2).trans hsp₄
  have r5 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x21, .x25, .x26, .x27]) :
      t₅.getReg r = u.getReg r := by
    rw [hpres₅.reg r (mem_of_mem hr _), k₄ r (mem_of_mem hr _), hpres₃.reg r (mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have r6 (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x21, .x26, .x27]) :
      t₆.getReg r = u.getReg r := by
    rw [k₆ r (mem_of_mem hr _), r5 r (mem_of_mem hr _)]
  have hx20₅ : t₅.getReg .x20 = BitVec.ofNat 64 (6 - j) := by
    rw [hpres₅.reg .x20, k₄ .x20 (by decide), hpres₃.reg .x20, k₂ .x20 (by decide),
      b80009a90_x20 h₁, hc.x20]
    addr_omega [hj]
  have hx19₅ : t₅.getReg .x19 = 1 := (r5 .x19 (by decide)).trans hc.x19
  have hval' : Model.limbs (img ch (sv s i) (j + 1)) =
      (t₆.getReg .x25, t₆.getReg .x8, t₆.getReg .x18) := by
    rw [img_succ ch hl _ j hj, istage, limbs_add, hval, ← hv₅, limbs_eAt,
      b80009ad8_x25 h₆, b80009ad8_x8 h₆, b80009ad8_x18 h₆, hsp₅, r5 .x25 (by decide),
      r5 .x8 (by decide), r5 .x18 (by decide)]
    rv_eval [Prod.mk.injEq]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  have keep (a : Word) (h1 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 1584 ∨
      ((s.getReg .x2).toNat - 192 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 144)) :
      t₆.getMem a = u.getMem a := by
    rw [hm₆, hf₅ _ (by addr_omega [h1, hb]) (by addr_omega [h1, hb]), hm₄,
      hf₃ _ (by addr_omega [h1, hb]) (by addr_omega [h1, hb]) (by addr_omega [h1, hb]),
      hm₂ _ (by addr_omega [h1, hb]), hm₁]
  have ph₆ := ph₅.same hm₆ (k₆ .x2 (by decide))
  have hbuf (l : Nat) (hl : l < i) : eAt t₆ (I + BitVec.ofNat 64 (24 * l)) =
      ringMapRust (sv s l) ch := by
    have hi := hc.lt
    simp only [nS] at hi
    rcases hI with hI | hI
    · omega
    rw [eAt_congr (keep _ (Or.inl (by addr_omega [hl, hi, hI.2, hH, hb])))
      (keep _ (Or.inl (by addr_omega [hl, hi, hI.2, hH, hb])))
      (keep _ (Or.inl (by addr_omega [hl, hi, hI.2, hH, hb])))]
    exact hc.buf l hl
  have hregs : IRegs s t₆ := {
    x9 := (r6 .x9 (by decide)).trans hc.x9
    x19 := (r6 .x19 (by decide)).trans hc.x19
    x27 := (r6 .x27 (by decide)).trans hc.x27 }
  by_cases h5 : j + 1 = 6
  · have hpc₆ := b80009ad8_pc_not_taken h₆ (by rw [hx20₅, hx19₅]; addr_omega [h5])
    obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80009afc_spec hpc₆ trivial
    have k₇ := b80009afc_keeps h₇
    have hm₇ := b80009afc_mem_same h₇
    have r7 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x21, .x25, .x26, .x27]) :
        t₇.getReg r = t₆.getReg r := k₇ r (mem_of_mem hr _)
    refine ⟨t₇, hr₁.trans (hr₃.trans (hr₅.trans (hr₆.trans hr₇))), Or.inr (Or.inr ⟨h5, {
      x9 := (r7 .x9 (by decide)).trans hregs.x9
      x19 := (r7 .x19 (by decide)).trans hregs.x19
      x27 := (r7 .x27 (by decide)).trans hregs.x27
      ph := ph₆.same hm₇ (k₇ .x2 (by decide))
      pc := b80009afc_pc h₇
      lt := hc.lt
      x21 := by rw [r7 .x21 (by decide), r6 .x21 (by decide), hc.x21]
      x26 := by rw [r7 .x26 (by decide), r6 .x26 (by decide), hc.x26]
      val := by
        rw [r7 .x25 (by decide), r7 .x8 (by decide), r7 .x18 (by decide), ← hval', h5]
      buf := fun l hl ↦ by simp only [eAt, hm₇]; exact hbuf l hl }⟩)⟩
  · refine ⟨t₆, hr₁.trans (hr₃.trans (hr₅.trans hr₆)), Or.inr (Or.inl ⟨by omega, {
      toIRegs := hregs
      ph := ph₆
      pc := b80009ad8_pc_taken h₆ (by rw [hx20₅, hx19₅]; addr_omega [h5, hj])
      lt := hc.lt
      ltj := by omega
      x21 := (r6 .x21 (by decide)).trans hc.x21
      x26 := (r6 .x26 (by decide)).trans hc.x26
      x20 := by rw [k₆ .x20 (by decide), hx20₅]; addr_omega [hj, h5]
      x10 := by
        rw [b80009ad8_x10 h₆, hpres₅.reg .x24, k₄ .x24 (by decide), hpres₃.reg .x24, b80009a98_x24 h₂, hx10₁]
        addr_omega [hj, hb]
      x22 := by
        rw [b80009ad8_x22 h₆, hpres₅.reg .x23, k₄ .x23 (by decide), hpres₃.reg .x23, b80009a98_x23 h₂,
          k₁ .x22 (by decide), hc.x22]
        addr_omega [hj, hcC, hC, hH]
      val := hval'
      shifts := fun i hi ↦ by
        rw [keep _ (Or.inr ⟨by addr_omega [hi, hb], by addr_omega [hi, hb]⟩)]
        exact hc.shifts i hi
      buf := hbuf }⟩)⟩

end

end Rv64Verifier.Proofs.Pcs.RingSwitch
