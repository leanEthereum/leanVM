import Rv64Verifier.Proofs.Transcript.SumcheckSample

/-!
# `transcript::sumcheck`'s rounds: the push and the new claim

From `0x800105e0`: the challenge appended to the point, `poly_eval` of the message at it into the
claim, then on to the loop head after `i + 1` rounds, or to the exit after the last.
-/

namespace Rv64Verifier.Transcript.Sumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F76
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem ofNat_succ_mul (k i : Nat) :
    (BitVec.ofNat 64 (k * (i + 1)) : Word) = BitVec.ofNat 64 (k * i) + BitVec.ofNat 64 k := by
  rw [show k * (i + 1) = k * i + k by ring, BitVec.ofNat_add]

theorem ofNat_sub32 {m : Nat} (h1 : 1 ≤ m) (h2 : 32 * m < 2 ^ 64) :
    (BitVec.ofNat 64 (32 * m) : Word) - 32 = BitVec.ofNat 64 (32 * (m - 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (32 : Word).toNat = 32 from rfl]
  omega

theorem add_succ_mul (a : Word) (k i : Nat) :
    a + BitVec.ofNat 64 (k * i) + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k * (i + 1)) := by
  rw [ofNat_succ_mul, BitVec.add_assoc]

set_option maxHeartbeats 4000000 in
/-- The push, `poly_eval`, and the loop's test. -/
theorem push (hP : PolyEvalSpec) {s u : MachineState} {ptr : Word} {i : Nat}
    (hpre : SumcheckPre s) (hpc : u.pc = 0x800105e0) (h : Chal s u ptr i) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨
      ((i + 1 < (s.getReg .x15).toNat → v.pc = 0x8001062c ∧ Inv s v ptr (i + 1)) ∧
       (i + 1 = (s.getReg .x15).toNat → v.pc = 0x80010698 ∧ Exit s v ptr))) := by
  have hb := bounds hpre
  have hS : 208 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hself := hpre.selfStack
  have hSelf := hpre.self.self
  have hcl := hpre.claim
  have hbuf := h.buf
  simp only [NewBuf] at hbuf
  have hlt := h.lt
  have hnl := n_lt hpre
  have hhi := h.fr.heap.hi
  have hlo := hpre.heap.lo
  have hmono := h.fr.mono
  have x2 := h.fr.saved.x2
  have b24 : ptr.toNat + 24 * i + 24 ≤ heapNext u := by
    rcases hbuf.2 with h0 | h0 <;> omega
  have hpl : heapNext s ≤ ptr.toNat := by rcases hbuf.2 with h0 | h0 <;> omega
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800105e0_spec hpc (by
    rv_eval [x2, h.x24, h.x25]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | addr_omega [hb, b24, hpl, hlo, hhi, hst.above]
      | (refine Samples.heap_valid ?_ ?_ ?_ <;> addr_omega [hb, b24, hpl, hlo, hhi, hbuf]))
  have k₁ := b800105e0_keeps h₁
  have m24 := b800105e0_m_x2_24 h₁
  have m1 := b800105e0_m1 h₁
  have m2 := b800105e0_m2 h₁
  have m3 := b800105e0_m3 h₁
  rw [x2, h.x26, show s.getReg .x2 - 208 + 24 = s.getReg .x2 - 184 by ring] at m24
  rw [x2, h.x24, h.x25, show s.getReg .x2 - 208 + 80 = s.getReg .x2 - 128 by ring] at m1
  rw [x2, h.x24, h.x25, show s.getReg .x2 - 208 + 88 = s.getReg .x2 - 128 + 8 by ring] at m2
  rw [x2, h.x24, h.x25, show s.getReg .x2 - 208 + 96 = s.getReg .x2 - 128 + 16 by ring] at m3
  have f₁ : DFrame u c fun a ↦ Within a (s.getReg .x2 - 184) 8 ∨
      Within a (ptr + BitVec.ofNat 64 (24 * i)) 24 :=
    DFrame.of_two fun a h1 h2 ↦ h₁.frame a (by
      rv_eval [x2, h.x24, h.x25]
      and_intros <;> addr_omega [h1, h2, hb, b24])
  have nx₁ : heapNext c = heapNext u := by
    simp only [heapNext]
    rw [f₁ _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb, hst.next, b24, hhi]]
  have F₁ : Fr s c := h.fr.step (by omega) (k₁ .x2 (by decide)) ⟨nx₁ ▸ h.fr.heap.lo, nx₁ ▸ hhi⟩
    (Nat.le_of_eq nx₁.symm) f₁ (fun a hw ↦ by
      rcases hw with hw | hw
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hw, hpl, b24, hhi], by addr_omega [hw, b24, nx₁, hhi]⟩))))
    fun y h1 h2 j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, h1, h2, hb, b24, hhi, hst.above]
  have x10c : c.getReg .x10 = s.getReg .x12 := (b800105e0_x10 h₁).trans h.x9
  have x11c : c.getReg .x11 = u.getReg .x23 := b800105e0_x11 h₁
  have x12c : c.getReg .x12 = u.getReg .x22 := b800105e0_x12 h₁
  have x13c : c.getReg .x13 = s.getReg .x2 - 128 := by
    rw [b800105e0_x13 h₁, x2]; ring
  have x2c : c.getReg .x2 = s.getReg .x2 - 208 := (k₁ .x2 (by decide)).trans x2
  have hmb := h.mbuf
  have hm := hst.mapped (by decide) (by decide)
  have hrod := hst.rodata
  have hpp : PolyEvalPre c := {
    out := by rw [x10c]; exact hcl
    coeffs := by
      rw [x11c, x12c]
      rcases hmb with h0 | ⟨b1, b2, b3⟩
      · exact Or.inl h0
      · exact Or.inr (by addr_omega [b1, b2, b3, hpl, hlo, hhi])
    point := by rw [x13c]; addr_omega [hb, hm]
    stack := hst.sub 208 x2c (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [x10c]; simp only [stackLo, x2c]; addr_omega [hpre.claimStack, hb]
    coeffsStack := by
      rw [x11c, x12c]; simp only [stackLo, x2c]
      rcases hmb with h0 | ⟨b1, b2, b3⟩
      · rw [h0]; exact Or.inl rfl
      · addr_omega [b1, b2, b3, hb, hst.above, hhi]
    pointStack := by rw [x13c]; simp only [stackLo, x2c]; addr_omega [hb]
    outCoeffs := by
      rw [x10c, x11c, x12c]
      rcases hmb with h0 | ⟨b1, b2, b3⟩
      · rw [h0]; exact Or.inr (Or.inl rfl)
      · addr_omega [b1, b2, b3, hpre.claimFree, hcl, hpl, hhi]
    outPoint := by rw [x10c, x13c]; addr_omega [hpre.claimStack, hb]
    rodata := V.rodata hpre F₁.heap.hi F₁.frame
    outRodata := by rw [x10c]; exact hpre.claimRodata }
  obtain ⟨t, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hP.call hr₁ (b800105e0_pc h₁) hpp
  swap
  · exact ⟨t, hr₂, Or.inl hd⟩
  have G₂ := hpost₂.frame
  rw [x10c] at G₂
  simp only [stackLo, x2c] at G₂
  have val₂ := hpost₂.value
  rw [x10c, x11c, x12c, x13c] at val₂
  have nx₂ : heapNext t = heapNext c := by
    simp only [heapNext]
    rw [G₂ _ fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hb, hst.next, hpre.claimFree, hcl]]
  have F₂ : Fr s t := F₁.step (by omega) (hpres₂.reg .x2) ⟨nx₂ ▸ F₁.heap.lo, nx₂ ▸ F₁.heap.hi⟩
    (Nat.le_of_eq nx₂.symm) G₂ (fun a hw ↦ by
      rcases hw with hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb]))))
    fun y h1 h2 j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, h1, h2, hb, hpre.claimStack, hcl]
  obtain ⟨v, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010620_spec
    (by rw [hpc₂, returnAddress_eq, b800105e0_x1 h₁]; decide) trivial
  have k₃ := b80010620_keeps h₃
  have hm₃ := b80010620_mem_same h₃
  have F₃ : Fr s v := F₂.same (by omega) (k₃ .x2 (by decide)) hm₃
  have nxv : heapNext v = heapNext u := by
    rw [show heapNext v = heapNext t by simp only [heapNext, hm₃], nx₂, nx₁]
  -- the registers
  have rk (r : Reg) (hr : r ∈ calleeSaved) (h3 : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22,
      .x23, .x24, .x26]) : v.getReg r = c.getReg r := by
    rw [k₃ r (mem_of_mem h3 _), hpres₂.reg r hr]
  have x27t : t.getReg .x27 = BitVec.ofNat 64 (32 * ((s.getReg .x15).toNat - i)) := by
    rw [hpres₂.reg .x27, k₁ .x27 (by decide), h.x27]
  have e27 : t.getReg .x27 - 32 = BitVec.ofNat 64 (32 * ((s.getReg .x15).toNat - (i + 1))) := by
    rw [x27t, ofNat_sub32 (by omega) (by omega)]
    congr 2
  -- the memory
  have keepM (y : Word) (h1 : (s.getReg .x2).toNat - 208 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 184) : v.getMem y = u.getMem y := by
    rw [hm₃, G₂ y fun j hj hw ↦ by
        rcases hw with hw | hw <;> addr_omega [hw, hj, h1, h2, hb, hpre.claimStack, hcl],
      f₁ y fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, h1, h2, hb, b24, hhi, hst.above]]
  have lenv : v.getMem (s.getReg .x2 - 184) = BitVec.ofNat 64 (i + 1) := by
    rw [hm₃, G₂ _ fun j hj hw ↦ by
        rcases hw with hw | hw <;> addr_omega [hw, hj, hb, hpre.claimStack, hcl],
      m24, BitVec.ofNat_add]
    rfl
  have Gv : DFrame u v fun a ↦ Within a (s.getReg .x2 - 184) 8 ∨
      Within a (ptr + BitVec.ofNat 64 (24 * i)) 24 ∨ Within a (s.getReg .x12) 24 ∨
      Within a (s.getReg .x2 - 208 - BitVec.ofNat 64 polyEvalStack) polyEvalStack :=
    ((f₁.mono fun a ha ↦ by rcases ha with ha | ha; exact Or.inl ha; exact Or.inr (Or.inl ha)).trans
      (G₂.mono fun a ha ↦ by
        rcases ha with ha | ha; exact Or.inr (Or.inr (Or.inl ha)); exact Or.inr (Or.inr (Or.inr ha)))
      fun _ h ↦ h).trans (DFrame.of_same hm₃ _) fun _ h ↦ h
  have pv : eListAt v ptr (i + 1) = eListAt u ptr i ++ [eAt u (s.getReg .x2 - 128)] := by
    rw [Samples.eListAt_succ, Gv.eListAt fun j hj hw ↦ by
      rcases hw with hw | hw | hw | hw <;>
        addr_omega [hw, hj, hb, b24, hpl, hhi, hst.above, hpre.claimFree, hcl, hlo]]
    congr 2
    rw [(DFrame.of_same hm₃ fun _ ↦ False).eAt fun _ _ h ↦ h, (G₂.eAt fun j hj hw ↦ by
      rcases hw with hw | hw <;>
        addr_omega [hw, hj, hb, b24, hpl, hhi, hst.above, hpre.claimFree, hcl, hlo])]
    exact eAt_congr m1 m2 m3
  have cv : eAt v (s.getReg .x12) =
      polyEvalRust (eListAt u (u.getReg .x23) (u.getReg .x22).toNat) (eAt u (s.getReg .x2 - 128)) := by
    rw [(DFrame.of_same hm₃ fun _ ↦ False).eAt fun _ _ h ↦ h, val₂, f₁.eAt fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hb, b24, hhi, hst.above]]
    congr 1
    refine f₁.eListAt fun j hj hw ↦ ?_
    rcases hmb with h0 | ⟨b1, b2, b3⟩
    · rw [h0] at hj; omega
    · rcases hw with hw | hw <;> addr_omega [hw, hj, hb, b1, b2, b3, hhi, hst.above, hlt, b24]
  have tv (T : TState) (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt v (s.getReg .x11) T := by
    refine (Low.transcriptAt hpre F₂.heap.hi F₁.heap.hi F₁.frame (G₂.mono fun a ha ↦ ?_)
      (Low.transcriptAt hpre (hi := heapNext u) hhi hhi h.fr.frame (f₁.mono fun a ha ↦ ?_) hT)).congr hm₃
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · rcases ha with ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hpl, b24, hhi], by addr_omega [ha, b24, hhi]⟩))
  have value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T',
      (pre s (i + 1)).run T = some ((eListAt v ptr (i + 1), eAt v (s.getReg .x12)), T') ∧
      TranscriptAt v (s.getReg .x11) T' := fun T hT ↦ by
    obtain ⟨Ti, T', hrun, hq, hch, hT'⟩ := h.value T hT
    refine ⟨_, ?_, tv _ hT'⟩
    rw [pre_succ' s hlt, hrun, Option.bind_some, round_run, hq, Option.bind_some, pv, cv, hch]
  have x9v : v.getReg .x9 = s.getReg .x12 := by
    rw [rk .x9 (by decide) (by decide), k₁ .x9 (by decide), h.x9]
  have bufv : NewBuf s v ptr ((s.getReg .x15).toNat * 24) 8 := by
    have := h.buf; simp only [NewBuf, nxv] at this ⊢; exact this
  have outv : v.getMem (s.getReg .x2 - 208) = s.getReg .x10 := by
    rw [keepM _ (by addr_omega [hb]) (by addr_omega [hb]), h.outM]
  have capv : v.getMem (s.getReg .x2 - 200) = s.getReg .x15 := by
    rw [keepM _ (by addr_omega [hb]) (by addr_omega [hb]), h.capM]
  have ptrv : v.getMem (s.getReg .x2 - 192) = ptr := by
    rw [keepM _ (by addr_omega [hb]) (by addr_omega [hb]), h.ptrM]
  refine ⟨v, hr₂.trans hr₃, Or.inr ⟨fun hl ↦ ?_, fun he ↦ ?_⟩⟩
  · refine ⟨b80010620_pc_not_taken h₃ ?_, ⟨⟨F₃, ?_, x9v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, outv, capv, ptrv,
      lenv, bufv, hl⟩, value⟩⟩
    · rw [e27]
      intro h0
      rw [Samples.ofNat_eq_zero (by omega)] at h0
      omega
    · rw [rk .x8 (by decide) (by decide), k₁ .x8 (by decide), h.x8]
    · rw [rk .x18 (by decide) (by decide), b800105e0_x18 h₁, h.x18]
      exact add_succ_mul _ 32 i
    · rw [rk .x19 (by decide) (by decide), k₁ .x19 (by decide), h.x19]
    · rw [rk .x20 (by decide) (by decide), k₁ .x20 (by decide), h.x20]
    · rw [rk .x21 (by decide) (by decide), k₁ .x21 (by decide), h.x21]
    · rw [rk .x24 (by decide) (by decide), k₁ .x24 (by decide), h.x24]
    · rw [b80010620_x25 h₃, hpres₂.reg .x25, k₁ .x25 (by decide), h.x25]
      exact (ofNat_succ_mul 24 i).symm
    · rw [rk .x26 (by decide) (by decide), b800105e0_x26 h₁, h.x26, BitVec.ofNat_add]
      rfl
    · rw [b80010620_x27 h₃, e27]
  · have hn : BitVec.ofNat 64 (i + 1) = s.getReg .x15 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, he, Nat.mod_eq_of_lt (s.getReg .x15).isLt]
    refine ⟨b80010620_pc_taken h₃ (by rw [e27, ← he, Nat.sub_self]; rfl), ⟨F₃, x9v, outv, capv, ptrv,
      by rw [lenv, hn], bufv, fun T hT ↦ ?_⟩⟩
    rw [← he]
    exact value T hT

end Rv64Verifier.Transcript.Sumcheck
