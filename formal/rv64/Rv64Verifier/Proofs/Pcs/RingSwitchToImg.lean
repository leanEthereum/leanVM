import Rv64Verifier.Proofs.Pcs.RingSwitchImgBase

/-!
# `ring_switch`: the images' buffer

See `RingSwitchImgBase.lean`.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section
variable {s B1 u : MachineState} {C chP nx : Word} {ch : List E}

theorem toImages (hT : TryAllocZeroedSpec) (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch)
    (hd : CDone s B1 u C ch nx) :
    ∃ B2, Reaches Image.code u B2 ∧ (Dead Image.code B2 ∨ ∃ I, Ctx2 s B2 C chP I ch ∧
      B2.getReg .x21 = 0 ∧ ((nS s = 0 ∧ B2.pc = 0x80009b00) ∨ (nS s ≠ 0 ∧ B2.pc = 0x800099c0))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := hd.ph.sp.trans hctx.sp
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  have hcL := hctx.chLo
  have hcC := hctx.chC
  have hfit := hd.ph.fits
  have hmo := hd.ph.mono
  have kF (a : Word) (h1 : (s.getReg .x2).toNat - 464 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 312 ∨
        (s.getReg .x2).toNat - 104 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat) :
      u.getMem a = B1.getMem a := keepF hpre hctx hd.ph h1 h2
  -- the coefficients' `Vec` to `F + 152`, `try_allocate_in`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000994c_spec hd.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000994c_keeps h₁
  have hm₁ := b8000994c_frame h₁ (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm₁
  rv_eval [] at hm₁
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 464 := (k₁ .x2 (by decide)).trans hsp
  have hn : u.getMem (s.getReg .x2 - 432) = s.getReg .x13 :=
    (kF _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.sLen
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 224 := by rw [b8000994c_x10 h₁, hsp]; rv_eval []
  have hx11₁ : t₁.getReg .x11 = s.getReg .x13 := by
    rw [b8000994c_x11 h₁, hsp]; rv_eval []; exact hn
  have hx8₁ : t₁.getReg .x8 = s.getReg .x13 := by
    rw [b8000994c_x8 h₁, hsp]; rv_eval []; exact hn
  have e152 := b8000994c_m_x2_152 h₁
  have e160 := b8000994c_m_x2_160 h₁
  have e168 := b8000994c_m_x2_168 h₁
  rw [hsp] at e152 e160 e168
  rv_eval [hd.x22] at e152 e160 e168
  rw [kF _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hctx.cap] at e152
  rw [kF _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hctx.cbuf] at e160
  have hnx₁ : t₁.getMem nextAddr = nx := (hm₁ _ (by addr_omega [hb])).trans hd.ph.next
  have hn₁ : heapNext t₁ = nx.toNat := by simp only [heapNext, hnx₁]
  have hsl₁ : stackLo t₁ tryAllocStack = s.getReg .x2 - 512 := by
    simp only [stackLo, tryAllocStack, hsp₁]; rv_eval []
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b8000994c_pc h₁) {
    heap := ⟨by rw [hn₁]; have := hctx.heap.lo; omega, by rw [hn₁]; exact hfit⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b8000994c_x13 h₁]; decide
    size := by rw [b8000994c_x14 h₁]; decide
    stack := hst.sub 464 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [hx10₁]; simp only [Outside]; addr_omega [hb]
    outStack := by rw [hx10₁, hsl₁]; addr_omega [hb] }
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl₁] at hfr₂
  have hD₂ := DFrame.of_byteFrame hfr₂
  have hfit₂ := hpost₂.heap.hi
  have hmo₂ := hpost₂.mono
  rw [hn₁] at hmo₂
  -- `Err` traps
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009980_spec
    (by rw [hpc₂, returnAddress_eq, b8000994c_x1 h₁]; decide) (by
      rv_eval [hpres₂.reg .x2, hsp₁]
      valid_access hst.valid [hb])
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 464 := (hpres₂.reg .x2).trans hsp₁
  by_cases htag : t₂.getMem (s.getReg .x2 - 224) = 0
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inl (dead_of_fetch ?_)⟩
    rw [b80009980_pc_taken h₃ (by rw [hsp₂]; rv_eval []; exact htag)]
    exact trap
  have hm₃ := b80009980_mem_same h₃
  have k₃ := b80009980_keeps h₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁, hx11₁] at hcap
  rw [hx10₁, hx11₁, b8000994c_x14 h₁, b8000994c_x13 h₁] at hbuf
  simp only [NewBuf] at hbuf
  rv_eval [] at hcap hbuf
  obtain ⟨I, hI⟩ : ∃ I, I = t₂.getMem (s.getReg .x2 - 208) := ⟨_, rfl⟩
  rw [← hI] at hbuf
  -- the images' `Vec`, `reserve(n)`
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 464 := (k₃ .x2 (by decide)).trans hsp₂
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009988_spec
    (b80009980_pc_not_taken h₃ (by rw [hsp₂]; rv_eval []; exact htag)) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b80009988_keeps h₄
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 248 := by rw [b80009988_x10 h₄, hsp₃]; rv_eval []
  have f232 := b80009988_m_x2_232 h₄
  have f224 := b80009988_m_x2_224 h₄
  have f216 := b80009988_m_x2_216 h₄
  have f0 := b80009988_m_x2_0 h₄
  rw [hsp₃] at f232 f224 f216 f0
  rv_eval [hm₃, hcap] at f232 f224 f216 f0
  have hD₄ : DFrame t₃ t₄ fun a ↦ Within a (s.getReg .x2 - 464) 8 ∨ Within a (s.getReg .x2 - 248) 24 :=
    fun a ha ↦ h₄.frame a (by
      have h0 := ha 0 (by decide)
      rw [add_ofNat_zero] at h0
      rv_eval [hsp₃]
      and_intros <;> intro he <;> rw [he] at h0 <;> exact h0 (by
        first
          | exact Or.inl (by addr_omega [hb])
          | exact Or.inr (by addr_omega [hb])))
  obtain ⟨t₅, hr₅, hpc₅, hpres₅, -, hm₅⟩ := MultilinearWords.reserve_fast (b80009988_pc h₄)
    (by rw [hx10₄]; valid_sub hst.valid [hb])
    (by
      rw [hx10₄, b80009988_x11 h₄, k₃ .x8 (by decide), hpres₂.reg .x8, hx8₁]
      rv_eval [f232, f216]; simp)
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 464 := (k₄ .x2 (by decide)).trans hsp₃
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 464 := (hpres₅.reg .x2).trans hsp₄
  obtain ⟨B2, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800099b0_spec
    (by rw [hpc₅, returnAddress_eq, b80009988_x1 h₄]; decide) (by
      rv_eval [hsp₅]
      and_intros <;> valid_access hst.valid [hb])
  have hm₆ := b800099b0_frame h₆ (by rw [hsp₅]; addr_omega [hb])
  rw [hsp₅] at hm₆
  rv_eval [] at hm₆
  have k₆ := b800099b0_keeps h₆
  have hnx₂ : heapNext t₂ ≤ heapEnd := hfit₂
  -- the frame from `u` and from `B1`
  have hD : DFrame u B2 fun a ↦ Within a (s.getReg .x2 - 512) 48 ∨ Within a (s.getReg .x2 - 464) 8 ∨
      Within a (s.getReg .x2 - 440) 8 ∨ Within a (s.getReg .x2 - 312) 112 ∨ Within a nextAddr 8 ∨
      (nx.toNat ≤ a.toNat ∧ a.toNat < heapNext t₂) :=
    (((((DFrame.of_memFrame hm₁).mono fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inl
      (by addr_omega [ha, hb]))))).trans hD₂ fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))
        · exact Or.inl ha
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
        · simp only [Fresh, hn₁] at ha; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha))))).trans
      (DFrame.of_same hm₃ fun _ ↦ False) fun _ h ↦ h.elim).trans hD₄ fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))).trans
      (DFrame.of_same hm₅ fun _ ↦ False) (fun _ h ↦ h.elim) |>.trans (DFrame.of_memFrame hm₆)
        fun a ha ↦ Or.inr (Or.inr (Or.inl ha))
  have hnB2 : B2.getMem nextAddr = t₂.getMem nextAddr := by
    rw [hm₆ _ (by addr_omega [hb]), hm₅, hD₄.word (fun x hx hW ↦ by
      rcases hW with hW | hW <;> addr_omega [hx, hW, hb]) (by decide), hm₃]
  have ph₆ := (hd.ph.widen (w' := fun a ↦ w1 s C a ∨ Within a (s.getReg .x2 - 464) 8 ∨
      Within a (s.getReg .x2 - 440) 8) fun a ha ↦ Or.inl ha).step hD
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha
      · exact Or.inr (Or.inl (by simp only [stackLo, hctx.sp]; addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (Or.inl ha))
      · exact Or.inl (Or.inr (Or.inr ha))
      · exact Or.inl (Or.inl (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapNext] at ha; exact ha.2⟩)))
    hnB2 (by simp only [heapNext] at hmo₂; exact hmo₂) hfit₂ (by rw [k₆ .x2 (by decide), hsp₅, hsp])
  have hHB2 : HeapOk B2 := ph₆.heap hctx.heap
  have hnB : heapNext B2 = heapNext t₂ := by simp only [heapNext, hnB2]
  have kB (a : Word) (h1 : (s.getReg .x2).toNat - 456 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 440 ∨
        ((s.getReg .x2).toNat - 432 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 312) ∨
        ((s.getReg .x2).toNat - 104 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat)) :
      B2.getMem a = B1.getMem a := by
    refine DFrame.word ph₆.mem (fun x hx hW ↦ ?_) (by addr_omega [h2, hb])
    rcases hW with ((hW | hW) | hW | hW) | hW | hW | hW
    · addr_omega [hW, hx, h1, h2, hb]
    · addr_omega [hW, hx, h1, hC, hH, hb]
    · addr_omega [hW, hx, h1, h2, hb]
    · addr_omega [hW, hx, h1, h2, hb]
    · simp only [stackLo, hctx.sp] at hW; addr_omega [hW, hx, h1, h2, hb]
    · addr_omega [hW, hx, h1, hb]
    · addr_omega [hW.2, hx, h1, hfit₂, hb]
  have kU (a : Word) (h1 : a.toNat + 8 ≤ nx.toNat) : B2.getMem a = u.getMem a :=
    hD.word (fun x hx hW ↦ by
      rcases hW with hW | hW | hW | hW | hW | hW
      · addr_omega [hW, hx, h1, hfit, hb]
      · addr_omega [hW, hx, h1, hfit, hb]
      · addr_omega [hW, hx, h1, hfit, hb]
      · addr_omega [hW, hx, h1, hfit, hb]
      · addr_omega [hW, hx, h1, hfit]
      · addr_omega [hW.1, hx, h1]) (by addr_omega [h1, hfit])
  have kT (a : Word) (h1 : (s.getReg .x2).toNat - 312 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 288) : B2.getMem a = t₁.getMem a := by
    rw [hm₆ a (by addr_omega [h1, h2, hb]), hm₅, hD₄.word (fun x hx hW ↦ by
      rcases hW with hW | hW <;> addr_omega [hW, hx, h1, h2, hb]) (by addr_omega [h2, hb]), hm₃,
      hD₂.word (fun x hx hW ↦ by
        rcases hW with hW | hW | hW | hW
        · addr_omega [hW, hx, h1, h2, hb]
        · addr_omega [hW, hx, h1, h2, hb]
        · addr_omega [hW, hx, h1, h2, hb]
        · simp only [Fresh] at hW; addr_omega [hW.2, hx, h1, h2, hfit₂, hb]) (by addr_omega [h2, hb])]
  have hx8₅ : t₅.getReg .x8 = s.getReg .x13 := by
    rw [hpres₅.reg .x8, k₄ .x8 (by decide), k₃ .x8 (by decide), hpres₂.reg .x8, hx8₁]
  have hIr := hbuf.2
  have hmB1 := hctx.mono
  have htr := tr_move hpre (Nat.le_trans hmB1 (by simp only [heapNext] at hmo ⊢; omega)) ph₆.mem
    hctx.sp hfit₂ (fun a ha ↦ by
      rcases ha with (ha | ha) | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (by addr_omega [ha, hC, hH, hcL, hcC])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])) (tr_ctx hpre hctx) hctx.tok
  have hmono : heapNext s ≤ heapNext B2 := by
    rw [hnB]; omega
  have hframe : DFrame s B2 fun a ↦ W0 s a ∨ Fresh s B2 a := by
    refine (hctx.frame.mono fun a ha ↦ ?_).trans ph₆.mem fun a ha ↦ ?_
    · rcases ha with ha | ha
      · exact Or.inl ha
      · simp only [Fresh] at ha ⊢; exact Or.inr ⟨ha.1, by have := ph₆.mono; rw [hnB]; omega⟩
    · rcases ha with ((ha | ha) | ha | ha) | ha | ha | ha
      · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr ⟨by addr_omega [ha, hcL, hcC], by rw [hnB]; addr_omega [ha, hC, hmo, hmo₂]⟩
      · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · simp only [stackLo, hctx.sp] at ha; exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inl (Or.inr (Or.inr ha))
      · exact Or.inr ⟨by omega, by rw [hnB]; simp only [heapNext] at ha ⊢; exact ha.2⟩
  refine ⟨B2, hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))), Or.inr ⟨I, {
    sp := (k₆ .x2 (by decide)).trans hsp₅
    heap := hHB2
    mono := hmono
    frame := hframe
    slots := fun p hp ↦ by
      have hb8 : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 ≤ 104 := by decide
      obtain ⟨h8, h104⟩ := hb8 p hp
      rw [kB _ (by addr_omega [h8, h104, hb]) (Or.inr (Or.inr ⟨by addr_omega [h8, h104, hb],
        by addr_omega [h8, h104, hb]⟩))]
      exact hctx.slots p hp
    pt := by
      rw [hm₆ _ (by addr_omega [hb]), hm₅, f0, k₃ .x23 (by decide), hpres₂.reg .x23,
        k₁ .x23 (by decide), hd.x23]
    out := by rw [kB _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hctx.out]
    sP := by rw [kB _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hctx.sP]
    iP := by
      have := b800099b0_m_x2_24 h₆
      rw [hsp₅] at this; rv_eval [] at this
      rw [this, hm₅, f224, hI]
    sLen := by rw [kB _ (by addr_omega [hb]) (Or.inr (Or.inl ⟨by addr_omega [hb],
      by addr_omega [hb]⟩)), hctx.sLen]
    chPm := by rw [kB _ (by addr_omega [hb]) (Or.inr (Or.inl ⟨by addr_omega [hb],
      by addr_omega [hb]⟩)), hctx.chPm]
    six := by rw [kB _ (by addr_omega [hb]) (Or.inr (Or.inl ⟨by addr_omega [hb],
      by addr_omega [hb]⟩)), hctx.six]
    c0 := by rw [kT _ (by addr_omega [hb]) (by addr_omega [hb]), e152]
    c1 := by rw [kT _ (by addr_omega [hb]) (by addr_omega [hb]), e160]
    c2 := by rw [kT _ (by addr_omega [hb]) (by addr_omega [hb]), e168]
    coeffs := fun l hl ↦ by
      rw [eAt_congr (kU _ (by addr_omega [hl, hC, hmo])) (kU _ (by addr_omega [hl, hC, hmo]))
        (kU _ (by addr_omega [hl, hC, hmo]))]
      exact hd.buf l hl
    chLen := hctx.chLen
    chs := by
      rw [← hctx.chs]
      refine DFrame.eList ph₆.mem (fun x hx hW ↦ ?_) (Or.inr (by addr_omega [hC, hH, hcC]))
      rcases hW with ((hW | hW) | hW | hW) | hW | hW | hW
      · addr_omega [hW, hx, hC, hH, hcC, hb]
      · addr_omega [hW, hx, hC, hH, hcC]
      · addr_omega [hW, hx, hC, hH, hcC, hb]
      · addr_omega [hW, hx, hC, hH, hcC, hb]
      · simp only [stackLo, hctx.sp] at hW; addr_omega [hW, hx, hC, hH, hcC, hb]
      · addr_omega [hW, hx, hC, hH, hcC]
      · addr_omega [hW.1, hx, hC, hmo, hcC]
    chA := hctx.chA
    chLo := hctx.chLo
    chC := hctx.chC
    cA := hctx.cA
    cHi := by rw [hnB]; omega
    iA := hbuf.1
    iR := by
      rcases hIr with h0 | ⟨h1, h2⟩
      · left; simp only [nS]; omega
      · right; simp only [nS]; rw [hnB]; rw [hn₁] at h1; omega
    tok := htr.1
    trEq := htr.2.1
    value := fun T hT ↦ by
      obtain ⟨T', hrun, hT'⟩ := hctx.value T hT
      exact ⟨T', hrun, htr.2.2 T' hT'⟩
    slices := slices_frame hpre hmono hHB2 hframe }, ?_, ?_⟩⟩
  · rw [b800099b0_x21 h₆, hsp₅]; rv_eval []; rw [hm₅, f232]
  · by_cases h0 : s.getReg .x13 = 0
    · exact Or.inl ⟨by simp only [nS, h0]; rfl, b800099b0_pc_taken h₆ (by rw [hx8₅, h0])⟩
    · refine Or.inr ⟨fun h ↦ h0 (BitVec.eq_of_toNat_eq (by simp only [nS] at h; simpa using h)),
        b800099b0_pc_not_taken h₆ (by rw [hx8₅]; exact h0)⟩

end

end Rv64Verifier.Proofs.Pcs.RingSwitch
