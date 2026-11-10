import Rv64Verifier.Proofs.Pcs.RingSwitchCoeffBase

/-!
# `ring_switch`: the coefficient loop

`cHead` (`0x8000986c`: the shifts, `acc = 1`), `cSkip` and `cMul` (a stage, without or with
`pow` and `mul`), `cTail` (`0x800098c4`: the next stage or the push), `cPush` (`0x8000982c`), and
the loops.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section
variable {s B1 u : MachineState} {C chP nx : Word} {ch : List E}

theorem cHead (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch) {k : Nat}
    (hh : CHead s B1 u C ch nx k) :
    ∃ v, Reaches Image.code u v ∧ CS s B1 v C chP ch nx 0x800098d4 k 0 0 := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := hh.ph.sp.trans hctx.sp
  have hx20 := hh.x20
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000986c_spec hh.pc (by
    rv_eval [hsp, hx20]
    and_intros <;> first | valid_access hst.valid [hb] | addr_omega [hb])
  have hsix : u.getMem (s.getReg .x2 - 416) = 6 :=
    (keepF hpre hctx hh.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.six
  have hpc₁ := b8000986c_pc_not_taken h₁ (by rw [hsp]; rv_eval [hsix]; decide)
  have hm₁ : MemFrame u t₁ (s.getReg .x2 - 312) 208 :=
    h₁.memFrame (by rv_eval [hsp, hx20]; and_intros <;> addr_omega [hb])
  have k₁ := b8000986c_keeps h₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800098b4_spec hpc₁ (by
    rv_eval [k₁ .x2 (by decide), hsp]
    valid_access hst.valid [hb])
  have k₂ := b800098b4_keeps h₂
  have hm₂ := b800098b4_mem_same h₂
  have m (a : Word) (h : ¬ Within a (s.getReg .x2 - 312) 208) : t₂.getMem a = u.getMem a := by
    rw [hm₂, hm₁ a h]
  have r (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x22, .x23, .x24, .x26, .x27]) :
      t₂.getReg r = u.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have e (c : Word) (v : Word) (h : t₁.getMem (u.getReg .x2 + c) = v) :
      t₂.getMem (s.getReg .x2 - 464 + c) = v := by rw [hm₂, ← hsp, h]
  have a0 := e _ _ (b8000986c_m_x2_152 h₁)
  have a1 := e _ _ (b8000986c_m_x2_160 h₁)
  have a2 := e _ _ (b8000986c_m_x2_168 h₁)
  have f (c : Word) (v : Word) (h : t₁.getMem (u.getReg .x20 + c) = v) :
      t₂.getMem (s.getReg .x2 - 192 + c) = v := by rw [hm₂, ← hx20, h]
  have s0 : t₂.getMem (s.getReg .x2 - 192) = 32 := by
    rw [hm₂, ← hx20, b8000986c_m_x20_0 h₁, hh.x19]
  have s1 := f _ _ (b8000986c_m_x20_8 h₁)
  have s2 := f _ _ (b8000986c_m_x20_16 h₁)
  have s3 := f _ _ (b8000986c_m_x20_24 h₁)
  have s4 := f _ _ (b8000986c_m_x20_32 h₁)
  have s5 := f _ _ (b8000986c_m_x20_40 h₁)
  rv_eval [hh.x18] at a0 a1 a2 s1 s2 s3 s4 s5
  refine ⟨t₂, hr₁.trans hr₂, {
    x9 := (r .x9 (by decide)).trans hh.x9
    x18 := (r .x18 (by decide)).trans hh.x18
    x19 := (r .x19 (by decide)).trans hh.x19
    x20 := (r .x20 (by decide)).trans hh.x20
    x23 := (r .x23 (by decide)).trans hh.x23
    x24 := (r .x24 (by decide)).trans hh.x24
    x27 := (r .x27 (by decide)).trans hh.x27
    ph := (hh.ph.step (DFrame.of_memFrame hm₁) (fun a ha ↦ Or.inl (Or.inl ha))
      ((hm₁ _ (by addr_omega [hb])).trans hh.ph.next)
      (Nat.le_refl _) hh.ph.fits (k₁ .x2 (by decide))).same hm₂ (k₂ .x2 (by decide))
    pc := b800098b4_pc h₂
    lt := hh.lt
    ltj := by decide
    x22 := (r .x22 (by decide)).trans hh.x22
    x26 := (r .x26 (by decide)).trans hh.x26
    x8 := by rw [b800098b4_x8 h₂, k₁ .x20 (by decide), hx20]; simp
    x21 := by rw [b800098b4_x21 h₂, k₁ .x27 (by decide), hh.x27]; rfl
    x25 := by
      rw [b800098b4_x25 h₂, k₁ .x2 (by decide), hsp, hm₁ _ (by rv_eval []; addr_omega [hb])]
      rv_eval []
      rw [keepF hpre hctx hh.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hctx.chPm]
      simp
    acc := by
      apply eAt_eq_of_limbs
      rw [cacc_zero, limbs_one]
      rv_eval [a0, a1, a2]
    shifts := shifts_of s0 s1 s2 s3 s4 s5
    buf := fun l hl ↦ by
      rw [eAt_congr (m _ (by addr_omega [hl, hh.lt, hC, hH, hb]))
        (m _ (by addr_omega [hl, hh.lt, hC, hH, hb])) (m _ (by addr_omega [hl, hh.lt, hC, hH, hb]))]
      exact hh.buf l hl }⟩

theorem rodataB1 (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch) : RodataOk B1 := by
  have hb := bounds hpre
  have hTr := hpre.self.rodata
  have hH := hctx.heap.hi
  have hP := Region.bounds hpre.self.ok.self
  simp only [transcriptSize] at hP
  refine hpre.rodata.dframe hctx.frame fun a ha hW ↦ ?_
  rcases hW with (hW | hW | hW) | hW
  · addr_omega [ha, hW, hTr, hP]
  · addr_omega [ha, hW, hb]
  · addr_omega [ha, hW]
  · simp only [Fresh] at hW; addr_omega [ha, hW.2, hH]

theorem rodataU (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch) (h : Ph B1 u (w1 s C) nx) :
    RodataOk u := by
  have hb := bounds hpre
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  refine h.rodata (rodataB1 hpre hctx) (fun a ha hr ↦ ?_) (by simp only [stackLo, hctx.sp]; addr_omega [hb])
  rcases ha with ha | ha
  · addr_omega [ha, hr, hb]
  · addr_omega [ha, hr, hC, hH]

theorem shift_ne (j : Nat) (hj : j < 6) : shiftW j ≠ 0 := by
  intro h0
  have := congrArg BitVec.toNat h0
  rw [shift_toNat j hj, show (0 : Word).toNat = 0 from rfl] at this
  have := shift_pos j hj
  omega

theorem CS.retarget {pc pc' : Word} {k j a a' : Nat} (h : CS s B1 u C chP ch nx pc k j a)
    (hpc : u.pc = pc') (e : cacc ch k a = cacc ch k a') : CS s B1 u C chP ch nx pc' k j a' :=
  { h with pc := hpc, acc := h.acc.trans e }

/-- A stage with `k & shift ≠ 0`, from `0x800098e0`: the challenge and `acc` copied,
`pow(F + 216, F + 336, 1 << (k % shift))`, `mul(F + 152, F + 176, F + 216)`. -/
theorem cMul (hP : PowSpec) (hM : MulSpec) (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch)
    {k j : Nat} (hc : CS s B1 u C chP ch nx 0x800098e0 k j j) (hx10 : u.getReg .x10 = shiftW j)
    (hz : k &&& ringMapShiftsRust.getD j 0 ≠ 0) :
    ∃ v, Reaches Image.code u v ∧
      (Dead Image.code v ∨ CS s B1 v C chP ch nx 0x800098c4 k j (j + 1)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := hc.ph.sp.trans hctx.sp
  have hj := hc.ltj
  have hk := hc.lt
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
  have hx25 := hc.x25
  -- copies of the challenge and `acc`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800098e0_spec hc.pc (by
    rv_eval [hsp, hx25]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access hchV [hj, hcC, hC, hH, hcA]
      | addr_omega [hj, hcC, hC, hH, hb])
  have hpc₂ := b800098e0_pc_not_taken h₂ (by rw [hx10]; exact shift_ne j hj)
  have hm₂ := b800098e0_frame h₂ (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm₂
  rv_eval [] at hm₂
  have k₂ := b800098e0_keeps h₂
  have c0 := b800098e0_m_x2_176 h₂
  have c1 := b800098e0_m_x2_184 h₂
  have c2 := b800098e0_m_x2_192 h₂
  have g0 := b800098e0_m_x2_336 h₂
  have g1 := b800098e0_m_x2_344 h₂
  have g2 := b800098e0_m_x2_352 h₂
  rw [hsp] at c0 c1 c2 g0 g1 g2
  rv_eval [] at c0 c1 c2 g0 g1 g2
  have eAcc : eAt t₂ (s.getReg .x2 - 288) = cacc ch k j := by
    rw [← hc.acc]; unfold eAt; rv_eval [c0, c1, c2]
  have eCh : eAt t₂ (s.getReg .x2 - 128) = ch.getD j 0 := by
    rw [← keepCh hpre hctx hc.ph hj, ← hx25]; unfold eAt; rv_eval [g0, g1, g2]
  have sh₂ (i : Nat) (hi : i < 6) : t₂.getMem (s.getReg .x2 - 192 + BitVec.ofNat 64 (8 * i)) =
      shiftW i := by
    rw [h₂.frame _ (by rv_eval [hsp, hx25]; and_intros <;> addr_omega [hi, hb])]
    exact hc.shifts i hi
  have ph₂ := hc.ph.step (DFrame.of_memFrame hm₂)
    (fun a ha ↦ Or.inl (Or.inl (by addr_omega [ha, hb])))
    ((hm₂ _ (by addr_omega [hb])).trans hc.ph.next) (Nat.le_refl _) hc.ph.fits
    (k₂ .x2 (by decide))
  -- `pow`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000991c_spec hpc₂ trivial
  have k₃ := b8000991c_keeps h₃
  have hm₃ := b8000991c_mem_same h₃
  have hx12₃ : t₃.getReg .x12 =
      t₂.getReg .x18 <<< ((rv64_remu (t₂.getReg .x26) (t₂.getReg .x10)).toNat % 64) :=
    h₃.reg_eq .x12 rfl (by rv_eval [])
  have hexp : (t₃.getReg .x12).toNat = 2 ^ (k % ringMapShiftsRust.getD j 0) := by
    have hp := shift_pos j hj
    have hlt := Nat.mod_lt k (show 0 < ringMapShiftsRust.getD j 0 by omega)
    rw [hx12₃, k₂ .x18 (by decide), hc.x18, k₂ .x26 (by decide), hc.x26, k₂ .x10 (by decide), hx10,
      remu_toNat j k hj hk]
    exact one_shl _ (by omega)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 464 := (k₂ .x2 (by decide)).trans hsp
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 464 := (k₃ .x2 (by decide)).trans hsp₂
  have hx10₃ : t₃.getReg .x10 = s.getReg .x2 - 248 := by rw [b8000991c_x10 h₃, hsp₂]; rv_eval []
  have hx11₃ : t₃.getReg .x11 = s.getReg .x2 - 128 := by rw [b8000991c_x11 h₃, hsp₂]; rv_eval []
  have hsl₃ : stackLo t₃ powStack = s.getReg .x2 - 1568 := by
    simp only [stackLo, powStack, mulStack, hsp₃, Nat.reduceAdd]; rv_eval []
  have ph₃ := ph₂.same hm₃ (k₃ .x2 (by decide))
  have hro₃ := rodataU hpre hctx ph₃
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hd⟩ := hP.call hr₃ (b8000991c_pc h₃) {
    out := by rw [hx10₃]; valid_sub hst.valid [hb]
    base := by rw [hx11₃]; valid_sub hst.valid [hb]
    stack := (hst.sub 464 hsp₃ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    pool := poolOk_of_rodata hro₃ (by rw [hsl₃]; simp only [powStack, mulStack]; addr_omega [hb])
    outBase := by rw [hx10₃, hx11₃]; addr_omega [hb]
    outStack := by rw [hx10₃, hsl₃]; simp only [powStack, mulStack]; addr_omega [hb]
    baseStack := by rw [hx11₃, hsl₃]; simp only [powStack, mulStack]; addr_omega [hb]
    basePool := by rw [hx11₃]; addr_omega [hb] }
  swap
  · exact ⟨t₄, hr₂.trans hr₄, Or.inl hd⟩
  have hv₄ := hpost₄.value
  rw [hx10₃, hx11₃, hexp] at hv₄
  have hf₄ := hpost₄.frame
  rw [hx10₃, hx11₃, hsl₃] at hf₄
  simp only [powStack, mulStack, Nat.reduceAdd] at hf₄
  have hD₄ := dframe_of_three hf₄
  have ph₄ := ph₃.step hD₄
    (fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by simp only [stackLo, hctx.sp]; addr_omega [ha, hb])))
    ((hf₄ _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])).trans ph₃.next)
    (Nat.le_refl _) ph₃.fits (hpres₄.reg .x2)
  -- `mul`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80009934_spec
    (by rw [hpc₄, returnAddress_eq, b8000991c_x1 h₃]; decide) trivial
  have k₅ := b80009934_keeps h₅
  have hm₅ := b80009934_mem_same h₅
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 464 := (hpres₄.reg .x2).trans hsp₃
  have hx10₅ : t₅.getReg .x10 = s.getReg .x2 - 312 := by rw [b80009934_x10 h₅, hsp₄]; rv_eval []
  have hx11₅ : t₅.getReg .x11 = s.getReg .x2 - 288 := by rw [b80009934_x11 h₅, hsp₄]; rv_eval []
  have hx12₅ : t₅.getReg .x12 = s.getReg .x2 - 248 := by rw [b80009934_x12 h₅, hsp₄]; rv_eval []
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 464 := (k₅ .x2 (by decide)).trans hsp₄
  have hsl₅ : stackLo t₅ mulStack = s.getReg .x2 - 1488 := by
    simp only [stackLo, mulStack, hsp₅]; rv_eval []
  have ph₅ := ph₄.same hm₅ (k₅ .x2 (by decide))
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hpost₆⟩ | hd⟩ := hM.call hr₅ (b80009934_pc h₅) {
    out := by rw [hx10₅]; valid_sub hst.valid [hb]
    lhs := by rw [hx11₅]; valid_sub hst.valid [hb]
    rhs := by rw [hx12₅]; valid_sub hst.valid [hb]
    stack := (hst.sub 464 hsp₅ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    outLhs := by rw [hx10₅, hx11₅]; addr_omega [hb]
    outRhs := by rw [hx10₅, hx12₅]; addr_omega [hb]
    outStack := by rw [hx10₅, hsl₅]; simp only [mulStack]; addr_omega [hb]
    lhsStack := by rw [hx11₅, hsl₅]; simp only [mulStack]; addr_omega [hb]
    rhsStack := by rw [hx12₅, hsl₅]; simp only [mulStack]; addr_omega [hb]
    rodata := rodataU hpre hctx ph₅
    stackRodata := by rw [hsl₅]; simp only [mulStack]; addr_omega [hb] }
  swap
  · exact ⟨t₆, hr₂.trans (hr₄.trans hr₆), Or.inl hd⟩
  have hv₆ := hpost₆.value
  rw [hx10₅, hx11₅, hx12₅] at hv₆
  have hf₆ := hpost₆.frame
  rw [hx10₅, hsl₅] at hf₆
  simp only [mulStack] at hf₆
  have hD₆ := dframe_of_two hf₆
  have ph₆ := ph₅.step hD₆
    (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by simp only [stackLo, hctx.sp]; addr_omega [ha, hb])))
    ((hf₆ _ (by addr_omega [hb]) (by addr_omega [hb])).trans ph₅.next)
    (Nat.le_refl _) ph₅.fits (hpres₆.reg .x2)
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80009948_spec
    (by rw [hpc₆, returnAddress_eq, b80009934_x1 h₅]; decide) trivial
  have k₇ := b80009948_keeps h₇
  have hm₇ := b80009948_mem_same h₇
  -- values
  have eAcc₅ : eAt t₅ (s.getReg .x2 - 288) = cacc ch k j := by
    calc eAt t₅ (s.getReg .x2 - 288) = eAt t₄ (s.getReg .x2 - 288) := by simp only [eAt, hm₅]
      _ = eAt t₃ (s.getReg .x2 - 288) :=
        hD₄.eAt' (fun x hx hW ↦ by rcases hW with h | h | h <;> addr_omega [hx, h, hb])
          (by addr_omega [hb])
      _ = eAt t₂ (s.getReg .x2 - 288) := by simp only [eAt, hm₃]
      _ = cacc ch k j := eAcc
  have ePow₅ : eAt t₅ (s.getReg .x2 - 248) = ch.getD j 0 ^ 2 ^ (k % ringMapShiftsRust.getD j 0) := by
    simp only [eAt, hm₅]
    rw [← eAt, hv₄, ← eCh]
    simp only [eAt, hm₃]
  have r (r : Reg) (hr : r ∈ calleeSaved) : t₇.getReg r = u.getReg r := by
    rw [k₇ r (mem_of_mem hr _), hpres₆.reg r hr, k₅ r (mem_of_mem hr _), hpres₄.reg r hr,
      k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _)]
  have keep (a : Word) (h1 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 1584 ∨
      ((s.getReg .x2).toNat - 192 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 144)) :
      t₇.getMem a = u.getMem a := by
    rw [hm₇, hf₆ _ (by addr_omega [h1, hb]) (by addr_omega [h1, hb]), hm₅,
      hf₄ _ (by addr_omega [h1, hb]) (by addr_omega [h1, hb]) (by addr_omega [h1, hb]), hm₃]
    rcases h1 with h1 | h1
    · exact hm₂ _ (by addr_omega [h1, hb])
    · exact h₂.frame _ (by rv_eval [hsp, hx25]; and_intros <;> addr_omega [h1, hb])
  refine ⟨t₇, hr₂.trans (hr₄.trans (hr₆.trans hr₇)), Or.inr {
    x9 := (r .x9 (by decide)).trans hc.x9
    x18 := (r .x18 (by decide)).trans hc.x18
    x19 := (r .x19 (by decide)).trans hc.x19
    x20 := (r .x20 (by decide)).trans hc.x20
    x23 := (r .x23 (by decide)).trans hc.x23
    x24 := (r .x24 (by decide)).trans hc.x24
    x27 := (r .x27 (by decide)).trans hc.x27
    ph := ph₆.same hm₇ (k₇ .x2 (by decide))
    pc := b80009948_pc h₇
    lt := hk
    ltj := hj
    x22 := (r .x22 (by decide)).trans hc.x22
    x26 := (r .x26 (by decide)).trans hc.x26
    x8 := (r .x8 (by decide)).trans hc.x8
    x21 := (r .x21 (by decide)).trans hc.x21
    x25 := (r .x25 (by decide)).trans hc.x25
    acc := by
      rw [cacc_succ ch hctx.chLen k j hj]
      simp only [cstage, hz, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [← eAcc₅, ← ePow₅, ← hv₆]
      simp only [eAt, hm₇]
    shifts := fun i hi ↦ by
      rw [keep _ (Or.inr ⟨by addr_omega [hi, hb], by addr_omega [hi, hb]⟩)]
      exact hc.shifts i hi
    buf := fun l hl ↦ by
      rw [eAt_congr (keep _ (Or.inl (by addr_omega [hl, hk, hC, hH, hb])))
        (keep _ (Or.inl (by addr_omega [hl, hk, hC, hH, hb])))
        (keep _ (Or.inl (by addr_omega [hl, hk, hC, hH, hb])))]
      exact hc.buf l hl }⟩

/-- A stage: `0x800098d4`, and where `k & shift ≠ 0`, `pow` and `mul`. -/
theorem cStep (hP : PowSpec) (hM : MulSpec) (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch)
    {k j : Nat} (hc : CS s B1 u C chP ch nx 0x800098d4 k j j) :
    ∃ v, Reaches Image.code u v ∧
      (Dead Image.code v ∨ CS s B1 v C chP ch nx 0x800098c4 k j (j + 1)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := hc.ph.sp.trans hctx.sp
  have hj := hc.ltj
  have hk := hc.lt
  have hx8 := hc.x8
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800098d4_spec hc.pc (by
    rv_eval [hx8]
    valid_access hst.valid [hj, hb])
  have hsh : u.getMem (u.getReg .x8) = shiftW j := by rw [hx8]; exact hc.shifts j hj
  have hm₁ := b800098d4_mem_same h₁
  have k₁ := b800098d4_keeps h₁
  have hand := and_toNat j k hj hk
  have hl := hctx.chLen
  by_cases hz : k &&& ringMapShiftsRust.getD j 0 = 0
  · have hpc := b800098d4_pc_taken h₁ (by
      rw [hsh, hc.x26]; apply BitVec.eq_of_toNat_eq; rw [hand, hz]; rfl)
    have r (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
        .x27]) : t₁.getReg r = u.getReg r := k₁ r (mem_of_mem hr _)
    refine ⟨t₁, hr₁, Or.inr {
      x9 := (r .x9 (by decide)).trans hc.x9
      x18 := (r .x18 (by decide)).trans hc.x18
      x19 := (r .x19 (by decide)).trans hc.x19
      x20 := (r .x20 (by decide)).trans hc.x20
      x23 := (r .x23 (by decide)).trans hc.x23
      x24 := (r .x24 (by decide)).trans hc.x24
      x27 := (r .x27 (by decide)).trans hc.x27
      ph := hc.ph.same hm₁ (k₁ .x2 (by decide))
      pc := hpc
      lt := hk
      ltj := hj
      x22 := (r .x22 (by decide)).trans hc.x22
      x26 := (r .x26 (by decide)).trans hc.x26
      x8 := (r .x8 (by decide)).trans hc.x8
      x21 := (r .x21 (by decide)).trans hc.x21
      x25 := (r .x25 (by decide)).trans hc.x25
      acc := by
        rw [cacc_succ ch hl k j hj]
        simp only [eAt, hm₁, cstage, hz, ne_eq, not_true_eq_false, ↓reduceIte]
        exact hc.acc
      shifts := fun i hi ↦ by rw [hm₁]; exact hc.shifts i hi
      buf := fun l hl ↦ by simp only [eAt, hm₁]; exact hc.buf l hl }⟩
  have hpc := b800098d4_pc_not_taken h₁ (by
    rw [hsh, hc.x26]; intro h0; apply hz; rw [← hand, h0]; rfl)
  have r (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : t₁.getReg r = u.getReg r := k₁ r (mem_of_mem hr _)
  obtain ⟨v, hv, hv'⟩ := cMul hP hM hpre hctx {
    x9 := (r .x9 (by decide)).trans hc.x9
    x18 := (r .x18 (by decide)).trans hc.x18
    x19 := (r .x19 (by decide)).trans hc.x19
    x20 := (r .x20 (by decide)).trans hc.x20
    x23 := (r .x23 (by decide)).trans hc.x23
    x24 := (r .x24 (by decide)).trans hc.x24
    x27 := (r .x27 (by decide)).trans hc.x27
    ph := hc.ph.same hm₁ (k₁ .x2 (by decide))
    pc := hpc
    lt := hk
    ltj := hj
    x22 := (r .x22 (by decide)).trans hc.x22
    x26 := (r .x26 (by decide)).trans hc.x26
    x8 := (r .x8 (by decide)).trans hc.x8
    x21 := (r .x21 (by decide)).trans hc.x21
    x25 := (r .x25 (by decide)).trans hc.x25
    acc := by simp only [eAt, hm₁]; exact hc.acc
    shifts := fun i hi ↦ by rw [hm₁]; exact hc.shifts i hi
    buf := fun l hl ↦ by simp only [eAt, hm₁]; exact hc.buf l hl } (by rw [b800098d4_x10 h₁, hsh]) hz
  exact ⟨v, hr₁.trans hv, hv'⟩

/-- `0x800098c4`: the next stage, or the push after the sixth. -/
theorem cTail (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch) {k j : Nat}
    (hc : CS s B1 u C chP ch nx 0x800098c4 k j (j + 1)) :
    ∃ v, Reaches Image.code u v ∧ ((j + 1 < 6 ∧ CS s B1 v C chP ch nx 0x800098d4 k (j + 1) (j + 1)) ∨
      (j + 1 = 6 ∧ CPush s B1 v C ch nx k)) := by
  have hb := bounds hpre
  have hj := hc.ltj
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  have hcC := hctx.chC
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b800098c4_spec hc.pc trivial
  have k₁ := b800098c4_keeps h
  have hm := b800098c4_mem_same h
  have r (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x22, .x23, .x24, .x26, .x27]) :
      v.getReg r = u.getReg r := k₁ r (mem_of_mem hr _)
  have hregs : CRegs s v C := {
    x9 := (r .x9 (by decide)).trans hc.x9
    x18 := (r .x18 (by decide)).trans hc.x18
    x19 := (r .x19 (by decide)).trans hc.x19
    x20 := (r .x20 (by decide)).trans hc.x20
    x23 := (r .x23 (by decide)).trans hc.x23
    x24 := (r .x24 (by decide)).trans hc.x24
    x27 := (r .x27 (by decide)).trans hc.x27 }
  have ph := hc.ph.same hm (k₁ .x2 (by decide))
  by_cases h5 : j + 1 = 6
  · refine ⟨v, hr, Or.inr ⟨h5, {
      toCRegs := hregs
      ph := ph
      pc := b800098c4_pc_taken h (by rw [hc.x21]; addr_omega [h5])
      lt := hc.lt
      x22 := (r .x22 (by decide)).trans hc.x22
      x26 := (r .x26 (by decide)).trans hc.x26
      acc := by simp only [eAt, hm]; rw [← h5]; exact hc.acc
      buf := fun l hl ↦ by simp only [eAt, hm]; exact hc.buf l hl }⟩⟩
  · refine ⟨v, hr, Or.inl ⟨by omega, {
      toCRegs := hregs
      ph := ph
      pc := b800098c4_pc_not_taken h (by rw [hc.x21]; addr_omega [h5, hj])
      lt := hc.lt
      ltj := by omega
      x22 := (r .x22 (by decide)).trans hc.x22
      x26 := (r .x26 (by decide)).trans hc.x26
      x8 := by rw [b800098c4_x8 h, hc.x8]; addr_omega [hj, hb]
      x21 := by rw [b800098c4_x21 h, hc.x21]; addr_omega [hj, h5]
      x25 := by rw [b800098c4_x25 h, hc.x25]; addr_omega [hj, hcC, hC, hH]
      acc := by simp only [eAt, hm]; exact hc.acc
      shifts := fun i hi ↦ by rw [hm]; exact hc.shifts i hi
      buf := fun l hl ↦ by simp only [eAt, hm]; exact hc.buf l hl }⟩⟩

theorem mul24 (k : ℕ) (hk : k < 64) :
    BitVec.ofNat 64 k * 16 + BitVec.ofNat 64 k * 8 = BitVec.ofNat 64 (24 * k) := by
  addr_omega [hk]

/-- `0x8000982c`: the push; the next coefficient, or the end. -/
theorem cPush (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch) {k : Nat}
    (hc : CPush s B1 u C ch nx k) :
    ∃ v, Reaches Image.code u v ∧ ((k + 1 < 64 ∧ CHead s B1 v C ch nx (k + 1)) ∨
      (k + 1 = 64 ∧ CDone s B1 v C ch nx)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hk := hc.lt
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  have hcA := hctx.cA
  have hcL := hctx.chLo
  have hcC := hctx.chC
  have hlo := hpre.heap.lo
  simp only [heapStart] at hlo
  have hCV : ValidMemRange C 192 :=
    MultilinearWords.heap_valid_range hcA (by simp only [heapStart]; omega)
      (by simp only [heapEnd] at hH ⊢; omega)
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := hc.ph.sp.trans hctx.sp
  have hx9 := hc.x9
  have hx22 := hc.x22
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000982c_spec hc.pc (by
    rv_eval [hsp, hx9, hx22]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access hCV [hk, hC, hH, hcA]
      | addr_omega [hk, hC, hH, hb])
  have k₁ := b8000982c_keeps h
  have hD : DFrame u v (w1 s C) := fun a ha ↦ h.frame a (by
    have h0 := ha 0 (by decide)
    rw [add_ofNat_zero] at h0
    simp only [w1] at h0
    rv_eval [hsp, hx9, hx22]
    and_intros <;> intro he <;> rw [he] at h0 <;> exact h0 (by
      first
        | exact Or.inl (by addr_omega [hb])
        | exact Or.inr (by addr_omega [hk, hC, hH])))
  have ph := hc.ph.step hD (fun a ha ↦ Or.inl ha)
    ((hD.word (fun x hx hW ↦ by rcases hW with hW | hW <;> addr_omega [hx, hW, hb, hC, hH])
      (by decide)).trans hc.ph.next) (Nat.le_refl _) hc.ph.fits (k₁ .x2 (by decide))
  have m0 := b8000982c_m0 h
  have m1 := b8000982c_m1 h
  have m2 := b8000982c_m2 h
  rw [hx9, hx22, mul24 k hk, hsp] at m0 m1 m2
  have hnew : eAt v (C + BitVec.ofNat 64 (24 * k)) = cacc ch k 6 := by
    rw [← hc.acc]; unfold eAt; rw [m0, m1, m2]; rv_eval []
  have keep (a : Word) (h1 : C.toNat ≤ a.toNat) (h2 : a.toNat + 8 ≤ C.toNat + 24 * k) :
      v.getMem a = u.getMem a :=
    h.frame a (by rv_eval [hsp, hx9, hx22]; and_intros <;> addr_omega [h1, h2, hk, hC, hH, hb])
  have hbuf (l : Nat) (hl : l < k + 1) : eAt v (C + BitVec.ofNat 64 (24 * l)) = cacc ch l 6 := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · rw [eAt_congr (keep _ (by addr_omega [hl, hk, hC, hH]) (by addr_omega [hl, hk, hC, hH]))
        (keep _ (by addr_omega [hl, hk, hC, hH]) (by addr_omega [hl, hk, hC, hH]))
        (keep _ (by addr_omega [hl, hk, hC, hH]) (by addr_omega [hl, hk, hC, hH]))]
      exact hc.buf l hl
    · exact hnew
  have r (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x23, .x24, .x27]) :
      v.getReg r = u.getReg r := k₁ r (mem_of_mem hr _)
  have hx26 : v.getReg .x26 = BitVec.ofNat 64 (k + 1) := by
    rw [b8000982c_x26 h, hc.x26]; addr_omega [hk]
  have hx22' : v.getReg .x22 = BitVec.ofNat 64 (k + 1) := by
    rw [b8000982c_x22 h, hc.x22]; addr_omega [hk]
  by_cases hk1 : k + 1 = 64
  · refine ⟨v, hr, Or.inr ⟨hk1, {
      ph := ph
      pc := b8000982c_pc_taken h (by rw [hc.x26, hc.x24]; addr_omega [hk1])
      x22 := by rw [hx22', hk1]; rfl
      x23 := (r .x23 (by decide)).trans hc.x23
      buf := fun l hl ↦ hbuf l (by omega) }⟩⟩
  · refine ⟨v, hr, Or.inl ⟨by omega, {
      x9 := (r .x9 (by decide)).trans hc.x9
      x18 := (r .x18 (by decide)).trans hc.x18
      x19 := (r .x19 (by decide)).trans hc.x19
      x20 := (r .x20 (by decide)).trans hc.x20
      x23 := (r .x23 (by decide)).trans hc.x23
      x24 := (r .x24 (by decide)).trans hc.x24
      x27 := (r .x27 (by decide)).trans hc.x27
      ph := ph
      pc := b8000982c_pc_not_taken h (by rw [hc.x26, hc.x24]; addr_omega [hk1, hk])
      lt := by omega
      x22 := hx22'
      x26 := hx26
      buf := hbuf }⟩⟩

/-- The stage loop: from stage `0` to the push. -/
theorem cStages (hP : PowSpec) (hM : MulSpec) (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch)
    {k : Nat} (h0 : CS s B1 u C chP ch nx 0x800098d4 k 0 0) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ CPush s B1 v C ch nx k) := by
  refine Reaches.loop (fun v ↦ ∃ j, CS s B1 v C chP ch nx 0x800098d4 k j j)
    (fun v ↦ 6 - (BitVec.toNat (v.getReg .x8) - BitVec.toNat (s.getReg .x2 - 192)) / 8)
    (fun v ↦ Dead Image.code v ∨ CPush s B1 v C ch nx k) ?_ u ⟨0, h0⟩
  rintro v ⟨j, hv⟩
  obtain ⟨w, hvw, hw⟩ := cStep hP hM hpre hctx hv
  rcases hw with hd | hw
  · exact Or.inl ⟨w, hvw, Or.inl hd⟩
  obtain ⟨x, hwx, hx⟩ := cTail hpre hctx hw
  rcases hx with ⟨hj, hx⟩ | ⟨-, hx⟩
  · refine Or.inr ⟨x, hvw.trans hwx, ⟨j + 1, hx⟩, ?_⟩
    have hb := bounds hpre
    rw [hx.x8, hv.x8]
    have h1 : (s.getReg .x2 - 192 + BitVec.ofNat 64 (8 * (j + 1))).toNat - (s.getReg .x2 - 192).toNat =
        8 * (j + 1) := by addr_omega [hj, hb]
    have h2 : (s.getReg .x2 - 192 + BitVec.ofNat 64 (8 * j)).toNat - (s.getReg .x2 - 192).toNat =
        8 * j := by addr_omega [hj, hb]
    rw [h1, h2]
    omega
  · exact Or.inl ⟨x, hvw.trans hwx, Or.inr hx⟩

/-- The coefficient loop: from `k = 0` to `0x8000994c`. -/
theorem cLoop (hP : PowSpec) (hM : MulSpec) (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch)
    (h0 : CHead s B1 u C ch nx 0) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ CDone s B1 v C ch nx) := by
  refine Reaches.loop (fun v ↦ ∃ k, CHead s B1 v C ch nx k)
    (fun v ↦ 64 - (v.getReg .x26).toNat)
    (fun v ↦ Dead Image.code v ∨ CDone s B1 v C ch nx) ?_ u ⟨0, h0⟩
  rintro v ⟨k, hv⟩
  obtain ⟨w, hvw, hw⟩ := cHead hpre hctx hv
  obtain ⟨x, hwx, hx⟩ := cStages hP hM hpre hctx hw
  rcases hx with hd | hx
  · exact Or.inl ⟨x, hvw.trans hwx, Or.inl hd⟩
  obtain ⟨y, hxy, hy⟩ := cPush hpre hctx hx
  rcases hy with ⟨hk, hy⟩ | ⟨-, hy⟩
  · refine Or.inr ⟨y, hvw.trans (hwx.trans hxy), ⟨k + 1, hy⟩, ?_⟩
    rw [hy.x26, hv.x26, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · exact Or.inl ⟨y, hvw.trans (hwx.trans hxy), Or.inr hy⟩

end

end Rv64Verifier.Proofs.Pcs.RingSwitch
