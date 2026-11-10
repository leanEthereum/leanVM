import Rv64Verifier.Proofs.Transcript.RoundPolyNoneSum
import Rv64Verifier.Proofs.Transcript.RoundPolySomeMul

/-!
# `sumcheck_round_poly`'s `None` path: the head

`0x8000c580`: the constant and `claim` plus the sum into the new buffer, the two `Vec`s to
`S - 152` (`Ready`, with two elements).
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem eListAt_two (u : MachineState) (p : Word) :
    eListAt u p 2 = [eAt u p, eAt u (p + 24)] := by
  rw [Samples.eListAt_succ, Samples.eListAt_succ]
  simp only [Nat.mul_zero, add_ofNat_zero, Nat.mul_one]
  rfl

set_option maxHeartbeats 2000000 in
theorem noneHead {s w : MachineState} (hpre : RoundPolyPre s)
    (htag : s.getMem (s.getReg .x14) = 0) (hpc : w.pc = 0x8000c580) (h : AtHeadN s w) :
    ∃ u, Reaches Image.code w u ∧ u.pc = 0x8000c5b4 ∧ Ready s u (w.getReg .x10) 2
      (w.getReg .x23) (w.getReg .x21) (w.getReg .x9).toNat := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have x2 := h.fr.saved.x2
  have hB := h.bAl
  have hBn := h.bNext
  have hBlo := h.bLo
  have hBhi : (w.getReg .x10).toNat + 48 ≤ heapEnd := hBn ▸ h.fr.heap.hi
  have hlo := hpre.heap.lo
  have hmw := h.fr.mono
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c580_spec hpc (by
    rv_eval [x2]
    and_intros <;> first
      | addr_omega [hb, hB, hBlo, hBhi, hlo]
      | valid_access hpre.stack.valid [hb]
      | (refine Samples.heap_valid ?_ ?_ ?_ <;> addr_omega [hB, hBlo, hBhi, hlo, hmw]))
  have k₁ := b8000c580_keeps h₁
  have fr₁ (a : Word) (h1 : ¬ Within a (s.getReg .x2 - 152) 48)
      (h2 : ¬ Within a (w.getReg .x10) 48) : u.getMem a = w.getMem a :=
    h₁.frame a (by
      rv_eval [x2]
      and_intros <;> addr_omega [h1, h2, hb, hBhi])
  have Gw : DFrame w u fun a ↦ Within a (stackLo s roundPolyStack) roundPolyStack ∨
      Within a (w.getReg .x10) 48 :=
    (DFrame.of_two fr₁).mono fun a hw ↦ by
      rcases hw with hw | hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr hw
  have nxu : heapNext u = heapNext w := by
    simp only [heapNext]
    rw [Gw _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hst.next, hBhi, hb, hlo, hBlo]]
  have hbf := h.buf
  have hroom := h.room
  have tailU : eListAt u (w.getReg .x21) (w.getReg .x9).toNat =
      eListAt w (w.getReg .x21) (w.getReg .x9).toNat :=
    Gw.eListAt fun i hi hw ↦ by
      rcases hbf.2 with h0 | h0
      · omega
      · rcases hw with hw | hw <;> addr_omega [hw, hi, h0, hroom, hb, hst.above, hBhi]
  have n8 := b8000c580_m_x2_8 h₁
  have n16 := b8000c580_m_x2_16 h₁
  have n24 := b8000c580_m_x2_24 h₁
  have n32 := b8000c580_m_x2_32 h₁
  have n40 := b8000c580_m_x2_40 h₁
  have n48 := b8000c580_m_x2_48 h₁
  rw [x2] at n8 n16 n24 n32 n40 n48
  have b0 := b8000c580_m_x10_0 h₁
  have b8 := b8000c580_m_x10_8 h₁
  have b16 := b8000c580_m_x10_16 h₁
  have b24 := b8000c580_m_x10_24 h₁
  have b32 := b8000c580_m_x10_32 h₁
  have b40 := b8000c580_m_x10_40 h₁
  refine ⟨u, hr₁, b8000c580_pc h₁, {
    fr := {
      saved := h.fr.saved.step hS (k₁ .x2 (by decide)) (fun r hr ↦ k₁ r (mem_of_mem hr _))
        fun y h1 h2 ↦ fr₁ y (by addr_omega [h1, h2, hb]) (by addr_omega [h1, h2, hb, hBhi, hst.above])
      x8 := (k₁ .x8 (by decide)).trans h.fr.x8
      heap := ⟨by rw [nxu]; exact h.fr.heap.lo, by rw [nxu]; exact h.fr.heap.hi⟩
      mono := by rw [nxu]; exact hmw
      frame := (h.fr.frame.mono fun a h ↦ V.mono (Nat.le_of_eq nxu.symm) h).trans Gw fun a hw ↦ by
        rcases hw with hw | hw
        · exact Or.inr (Or.inl hw)
        · exact Or.inr (Or.inr (Or.inr ⟨by addr_omega [hw, hBlo], by rw [nxu, hBn]; addr_omega [hw]⟩)) }
    lc := by rw [show s.getReg .x2 - 152 = s.getReg .x2 - 160 + 8 by ring, n8]; rfl
    lp := by rw [show s.getReg .x2 - 144 = s.getReg .x2 - 160 + 16 by ring, n16]
    ll := by rw [show s.getReg .x2 - 136 = s.getReg .x2 - 160 + 24 by ring, n24]; rfl
    rc := by rw [show s.getReg .x2 - 128 = s.getReg .x2 - 160 + 32 by ring, n32]
    rp := by rw [show s.getReg .x2 - 120 = s.getReg .x2 - 160 + 40 by ring, n40]
    rl := by rw [show s.getReg .x2 - 112 = s.getReg .x2 - 160 + 48 by ring, n48, ofNat_toNat_self]
    m2 := le_refl _
    bufB := by simp only [NewBuf]; refine ⟨hB, Or.inr ⟨hBlo, ?_⟩⟩; rw [nxu, hBn]
    room := hroom
    buf := by
      simp only [NewBuf]
      refine ⟨hbf.1, ?_⟩
      rcases hbf.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by rw [nxu, hBn]; omega⟩
    value := fun T hT ↦ by
      obtain ⟨x, T₁, T', h1, hx, h2, h3⟩ := h.value T hT
      refine ⟨T', ?_, Fr.transcriptAt hpre h.fr (by rw [nxu]; exact h.fr.heap.hi)
        (Gw.mono fun a hw ↦ by
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (Or.inr ⟨by addr_omega [hw, hBlo], by rw [nxu, hBn]; addr_omega [hw]⟩)) h3⟩
      rw [mirror_none htag, h1]
      simp only [Option.bind_some]
      rw [h2]
      simp only [Option.bind_some]
      rw [tailU, eListAt_two]
      have e0 : eAt u (w.getReg .x10) = x := eAt_eq_of_limbs (by rw [b0, b8, b16, hx])
      have e1 : eAt u (w.getReg .x10 + 24) = eAt s (s.getReg .x13) +
          sumE (eListAt w (w.getReg .x21) (w.getReg .x9).toNat) :=
        eAt_eq_of_limbs (by
          rw [show w.getReg .x10 + 24 + 8 = w.getReg .x10 + 32 by ring,
            show w.getReg .x10 + 24 + 16 = w.getReg .x10 + 40 by ring, b24, b32, b40, h.x11,
            h.x12, h.x13])
      rw [e0, e1] }⟩

end Rv64Verifier.Transcript.RoundPoly
