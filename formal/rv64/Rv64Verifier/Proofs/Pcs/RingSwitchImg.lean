import Rv64Verifier.Proofs.Pcs.RingSwitchImgHead

/-!
# `ring_switch`: the images loop

`iStart` (`0x800099c0`), `iHead` (`0x80009a24`: the value, the shifts), `iStage` (a stage: `pow`,
`mul`, the value `+=` it), `iPush` (`0x800099f4`), and the loops.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem mul24g (k : ℕ) (hk : 24 * k < 2 ^ 64) :
    BitVec.ofNat 64 k * 16 + BitVec.ofNat 64 k * 8 = BitVec.ofNat 64 (24 * k) := by
  addr_omega [hk]

section
variable {s B2 u : MachineState} {C chP I nx : Word} {ch : List E}

theorem iStart (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch) (hpc : B2.pc = 0x800099c0)
    (hx21 : B2.getReg .x21 = 0) (hn : nS s ≠ 0) :
    ∃ v, Reaches Image.code B2 v ∧ IHead s B2 v I ch (B2.getMem nextAddr) 0 := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hctx.sp
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b800099c0_spec hpc (by
    rv_eval [hsp]
    valid_access hst.valid [hb])
  have k := b800099c0_keeps h
  have h6 : B2.getMem (B2.getReg .x2 + 48) = 6 := by rw [hsp]; rv_eval []; exact hctx.six
  exact ⟨v, hr, {
    x9 := b800099c0_x9 h
    x19 := h.reg_eq .x19 rfl (by rv_eval [h6]; decide)
    x27 := by rw [b800099c0_x27 h, hsp]; rv_eval []
    ph := (Ph.refl hctx.heap _).same (b800099c0_mem_same h) (k .x2 (by decide))
    pc := b800099c0_pc h
    lt := by omega
    x21 := by rw [k .x21 (by decide), hx21]; rfl
    x26 := b800099c0_x26 h
    buf := fun l hl ↦ absurd hl (Nat.not_lt_zero l) }⟩

theorem iHead (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch) {i : Nat}
    (hh : IHead s B2 u I ch nx i) :
    ∃ v, Reaches Image.code u v ∧ IStage s B2 v chP I ch nx i 0 := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := hh.ph.sp.trans hctx.sp
  have hi := hh.lt
  have hx27 := hh.x27
  have hx26 := hh.x26
  have hR := hpre.slices.region.resolve_left (by simp only [nS] at hi; omega)
  have hRb := Region.bounds hR
  have hSs := hpre.slices.stack
  simp only [nS] at hi
  have hsP : u.getMem (s.getReg .x2 - 448) = s.getReg .x12 :=
    (keepF2 hpre hctx hh.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.sP
  have hsix : u.getMem (s.getReg .x2 - 416) = 6 :=
    (keepF2 hpre hctx hh.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.six
  have hchP : u.getMem (s.getReg .x2 - 424) = chP :=
    (keepF2 hpre hctx hh.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.chPm
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009a24_spec hh.pc (by
    rv_eval [hsp, hx27, hx26, hsP]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hR (by addr_omega [hRb, hi]) (by addr_omega [hRb, hi])
          (by addr_omega [hRb, hi])
      | addr_omega [hRb, hi, hSs, hb])
  have hpc₁ := b80009a24_pc_not_taken h₁ (by rw [hsp]; rv_eval [hsix]; decide)
  have hm₁ : MemFrame u t₁ (s.getReg .x2 - 288) 184 :=
    h₁.memFrame (by rv_eval [hsp, hx27]; and_intros <;> addr_omega [hb])
  have k₁ := b80009a24_keeps h₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009a84_spec hpc₁ (by
    rv_eval [k₁ .x2 (by decide), hsp]
    valid_access hst.valid [hb])
  have k₂ := b80009a84_keeps h₂
  have hm₂ := b80009a84_mem_same h₂
  have m (a : Word) (h : ¬ Within a (s.getReg .x2 - 288) 184) : t₂.getMem a = u.getMem a := by
    rw [hm₂, hm₁ a h]
  have f (c : Word) (v : Word) (h : t₁.getMem (u.getReg .x27 + c) = v) :
      t₂.getMem (s.getReg .x2 - 192 + c) = v := by rw [hm₂, ← hx27, h]
  have s0 : t₂.getMem (s.getReg .x2 - 192) = 32 := by rw [hm₂, ← hx27, b80009a24_m_x27_0 h₁]
  have s1 := f _ _ (b80009a24_m_x27_8 h₁)
  have s2 := f _ _ (b80009a24_m_x27_16 h₁)
  have s3 := f _ _ (b80009a24_m_x27_24 h₁)
  have s4 := f _ _ (b80009a24_m_x27_32 h₁)
  have s5 := f _ _ (b80009a24_m_x27_40 h₁)
  rv_eval [hh.x9] at s1 s2 s3 s4 s5
  have hv : Model.limbs (sv s i) = (t₂.getReg .x25, t₂.getReg .x8, t₂.getReg .x18) := by
    rw [← keepSl hpre hctx hh.ph (by simp only [nS]; exact hi), limbs_eAt,
      k₂ .x25 (by decide), k₂ .x8 (by decide), k₂ .x18 (by decide), b80009a24_x25 h₁,
      b80009a24_x8 h₁, b80009a24_x18 h₁, hsp, hx26]
    rv_eval [hsP]
    rw [mul24g i (by addr_omega [hRb, hi])]
  have r (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x21, .x26, .x27]) : t₂.getReg r = u.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hI := hctx.iR
  have hH := hctx.heap.hi
  simp only [nS] at hI
  refine ⟨t₂, hr₁.trans hr₂, {
    x9 := (r .x9 (by decide)).trans hh.x9
    x19 := (r .x19 (by decide)).trans hh.x19
    x27 := (r .x27 (by decide)).trans hh.x27
    ph := (hh.ph.step (DFrame.of_memFrame hm₁) (fun a ha ↦ Or.inl (Or.inl ha))
      ((hm₁ _ (by addr_omega [hb])).trans hh.ph.next) (Nat.le_refl _) hh.ph.fits
      (k₁ .x2 (by decide))).same hm₂ (k₂ .x2 (by decide))
    pc := b80009a84_pc h₂
    lt := by simp only [nS]; exact hi
    ltj := by decide
    x21 := (r .x21 (by decide)).trans hh.x21
    x26 := (r .x26 (by decide)).trans hh.x26
    x20 := b80009a84_x20 h₂
    x10 := by rw [b80009a84_x10 h₂, k₁ .x27 (by decide), hx27]; simp
    x22 := by
      rw [b80009a84_x22 h₂, k₁ .x2 (by decide), hsp, hm₁ _ (by rv_eval []; addr_omega [hb])]
      rv_eval []
      rw [hchP]; simp
    val := by rw [img_zero]; exact hv
    shifts := shifts_of s0 s1 s2 s3 s4 s5
    buf := fun l hl ↦ by
      have hl' : l < (s.getReg .x13).toNat := by omega
      rcases hI with hI | hI
      · omega
      rw [eAt_congr (m _ (by addr_omega [hl', hI.2, hH, hb])) (m _ (by addr_omega [hl', hI.2, hH, hb]))
        (m _ (by addr_omega [hl', hI.2, hH, hb]))]
      exact hh.buf l hl }⟩

end

end Rv64Verifier.Proofs.Pcs.RingSwitch
