import Rv64Verifier.Proofs.Transcript.RoundPolyCall

/-!
# `sumcheck_round_poly`'s end: the two `Vec`s, `concat`, the return

Both paths reach `0x8000c5b4` with the head's `Vec` (one or two elements, new) at `S - 152` and the
tail's at `S - 128` (`Ready`); `concat` makes the result.
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- At `0x8000c5b4`: the `Vec` of `m` elements in a new buffer `B` at `S - 152`, the tail's at
`S - 128`, and what the mirror returns. -/
structure Ready (s u : MachineState) (B : Word) (m : Nat) (cap ptr : Word) (len : Nat) : Prop where
  fr : Fr s u
  lc : u.getMem (s.getReg .x2 - 152) = BitVec.ofNat 64 m
  lp : u.getMem (s.getReg .x2 - 144) = B
  ll : u.getMem (s.getReg .x2 - 136) = BitVec.ofNat 64 m
  rc : u.getMem (s.getReg .x2 - 128) = cap
  rp : u.getMem (s.getReg .x2 - 120) = ptr
  rl : u.getMem (s.getReg .x2 - 112) = BitVec.ofNat 64 len
  m2 : m ≤ 2
  bufB : NewBuf s u B (m * 24) 8
  room : len ≤ cap.toNat
  buf : NewBuf s u ptr (cap.toNat * 24) 8
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T', (mirror s).run T =
    some (eListAt u B m ++ eListAt u ptr len, T') ∧ TranscriptAt u (s.getReg .x11) T'

set_option maxHeartbeats 1000000 in
/-- `concat` into the result, then return. -/
theorem finish (hC : ConcatSpec) {s u : MachineState} {B cap ptr : Word} {m len : Nat}
    (hpre : RoundPolyPre s) (hpc : u.pc = 0x8000c5b4) (h : Ready s u B m cap ptr len) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧ RoundPolyPost s t) ∨
      Dead Image.code t) := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have ho := hpre.out
  have hlo := hpre.heap.lo
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c5b4_spec hpc trivial
  have k₁ := b8000c5b4_keeps h₁
  have hm₁ := b8000c5b4_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 160 := (k₁ .x2 (by decide)).trans h.fr.saved.x2
  have x10₁ : u₁.getReg .x10 = s.getReg .x10 := (b8000c5b4_x10 h₁).trans h.fr.x8
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 152 := by
    rw [b8000c5b4_x11 h₁, h.fr.saved.x2]; ring
  have nx₁ : heapNext u₁ = heapNext u := by simp only [heapNext, hm₁]
  have e8 : s.getReg .x2 - 152 + 8 = s.getReg .x2 - 144 := by ring
  have e16 : s.getReg .x2 - 152 + 16 = s.getReg .x2 - 136 := by ring
  have e24 : s.getReg .x2 - 152 + 24 = s.getReg .x2 - 128 := by ring
  have e32 : s.getReg .x2 - 128 + 8 = s.getReg .x2 - 120 := by ring
  have e40 : s.getReg .x2 - 128 + 16 = s.getReg .x2 - 112 := by ring
  have hm64 : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.m2; omega)]
  have hlen64 : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h.room cap.isLt)]
  have hbB := h.bufB
  have hbuf := h.buf
  have hhi := h.fr.heap.hi
  have hmono := h.fr.mono
  simp only [NewBuf] at hbB hbuf
  have hcp : ConcatPre u₁ := {
    heap := ⟨nx₁ ▸ h.fr.heap.lo, nx₁ ▸ hhi⟩
    out := by rw [x10₁]; exact ho
    parts := by rw [x11₁]; addr_omega [hb]
    left := by
      rw [x11₁]
      refine ⟨?_, ?_⟩
      · simp only [RawVecOk, Buf, vecPtr, vecCap, e8, hm₁, h.lp, h.lc, hm64, nx₁]
        omega
      · simp only [vecLen, vecCap, e16, hm₁, h.ll, h.lc]; exact le_refl _
    right := by
      rw [x11₁, e24]
      refine ⟨?_, ?_⟩
      · simp only [RawVecOk, Buf, vecPtr, vecCap, e32, hm₁, h.rp, h.rc, nx₁]
        omega
      · simp only [vecLen, vecCap, e40, hm₁, h.rl, h.rc, hlen64]; exact h.room
    stack := hst.sub 160 x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hpre.outStack, hb]
    partsStack := by rw [x11₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    outFree := by rw [x10₁]; addr_omega [hpre.outFree, hmono, nx₁]
    partsFree := by rw [x11₁]; addr_omega [hst.above, hst.next, hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hC.call hr₁ (b8000c5b4_pc h₁) hcp
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c5c4_spec
    (by rw [hpc₂, returnAddress_eq, b8000c5b4_x1 h₁]; decide) trivial
  have k₃ := b8000c5c4_keeps h₃
  have hm₃ := b8000c5c4_mem_same h₃
  have G := hpost₂.frame
  rw [x10₁] at G
  simp only [stackLo, x2₁] at G
  have mono₂ := hpost₂.mono
  have hhi₂ := hpost₂.heap.hi
  have S₃ : Saved s t₃ := h.fr.saved.step hS
    (by rw [k₃ .x2 (by decide), hpres₂.reg .x2, k₁ .x2 (by decide)])
    (fun r hr ↦ by rw [k₃ r (mem_of_mem hr _), hpres₂.reg r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)])
    fun y h1 h2 ↦ by
      rw [hm₃, G y fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw <;>
          addr_omega [hw, hi, h1, h2, hb, ho, hpre.outStack, hst.next, hhi₂, hst.above], hm₁]
  obtain ⟨t, hr₄, pc, pres, hm⟩ := epilogue hpre (b8000c5c4_pc h₃) S₃
  have hmt (a : Word) : t.getMem a = t₂.getMem a := by rw [hm, hm₃]
  have nxt : heapNext t = heapNext t₂ := by simp only [heapNext, hmt]
  have hm1 : heapNext s ≤ heapNext u₁ := by rw [nx₁]; exact hmono
  have F₁ : DFrame s u₁ (W s u₁) :=
    (h.fr.frame.mono fun a h ↦ (V.mono (Nat.le_of_eq nx₁.symm) h).toW).trans
      (DFrame.of_same hm₁ _) fun _ h ↦ h
  have F₂ : DFrame s t₂ (W s t₂) := (F₁.mono fun a h ↦ TW.mono mono₂ h).trans G fun a hw ↦ by
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp only [Fresh] at hw; omega, hw.2⟩)))
  have Ft : DFrame s t (W s t) :=
    (F₂.mono fun a h ↦ TW.mono (Nat.le_of_eq nxt.symm) h).trans (DFrame.of_same hmt _) fun _ h ↦ h
  have hv := hpost₂.value
  rw [x10₁, x11₁, e24] at hv
  have el : vecEs u₁ (s.getReg .x2 - 152) = eListAt u B m := by
    simp only [vecEs, vecPtr, vecLen, e8, e16, hm₁, h.lp, h.ll, hm64]
    exact (DFrame.of_same hm₁ fun _ ↦ False).eListAt fun _ _ h ↦ h
  have er : vecEs u₁ (s.getReg .x2 - 128) = eListAt u ptr len := by
    simp only [vecEs, vecPtr, vecLen, e32, e40, hm₁, h.rp, h.rl, hlen64]
    exact (DFrame.of_same hm₁ fun _ ↦ False).eListAt fun _ _ h ↦ h
  rw [el, er] at hv
  have hcap := cap_ne_errNiche hv.buf hhi₂
  have hvo : VecOk t (s.getReg .x10) 24 8 := by
    refine ⟨?_, ?_⟩
    · have := hv.vec.raw
      simp only [RawVecOk, Buf, vecPtr, vecCap, nxt, hmt] at this ⊢
      exact this
    · have := hv.vec.len
      simp only [vecLen, vecCap, hmt] at this ⊢
      exact this
  have hnb : NewBuf s t (vecPtr t (s.getReg .x10)) ((vecCap t (s.getReg .x10)).toNat * 24) 8 := by
    have := hv.buf
    simp only [NewBuf, vecPtr, vecCap, hmt, nxt] at this ⊢
    omega
  have hcapt : vecCap t (s.getReg .x10) ≠ errNiche := by
    simp only [vecCap, hmt] at hcap ⊢; exact hcap
  refine ⟨t, hr₂.trans (hr₃.trans hr₄), Or.inl ⟨pc, pres, ⟨by rw [nxt]; exact hpost₂.heap.lo,
    by rw [nxt]; exact hhi₂⟩, by rw [nxt]; omega, fun T hT ↦ ?_, Ft, fun _ ↦ ⟨hvo, hnb⟩,
    fun he ↦ absurd he hcapt⟩⟩
  obtain ⟨T', hrun, hT'⟩ := h.value T hT
  simp only [mirror] at hrun
  rw [hrun]
  have hT₁ := Fr.transcriptAt (v := u₁) hpre h.fr (by rw [nx₁]; exact hhi) (DFrame.of_same hm₁ _) hT'
  have hT₂ := TLow.transcriptAt' hpre.toTPre hhi₂ (by rw [nx₁]; exact hhi) F₁ (G.mono fun a hw ↦ by
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl (by addr_omega [hw, hb]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp only [Fresh] at hw; omega, hw.2⟩))) hT₁
  refine ⟨hcapt, ⟨hvo, hnb, ?_⟩,
    TLow.transcriptAt hpre.toTPre hhi₂ hhi₂ F₂ (DFrame.of_same hmt _) hT₂⟩
  rw [show vecEs t (s.getReg .x10) = vecEs t₂ (s.getReg .x10) by
    simp only [vecEs, vecPtr, vecLen, hmt]
    exact (DFrame.of_same hmt fun _ ↦ False).eListAt fun _ _ h ↦ h]
  exact hv.elems

end Rv64Verifier.Transcript.RoundPoly
