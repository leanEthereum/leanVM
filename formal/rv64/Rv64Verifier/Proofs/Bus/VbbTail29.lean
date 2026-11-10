import Rv64Verifier.Proofs.Bus.VbbTail28

/-!
# `verify_bus_balance` past the side loop: the result and the return

At `0x80007c2c` one block copies the result into `a0`'s `BusResult`: `claims` from `S - 840`,
`bytecode_point` from `S - 768`, `point` from `S - 1320`, `s11` and `S - 1144`, `forms` from
`S - 1328`, `S - 1224` and `s9`, `totals` from `S - 632`; then the epilogue returns
(`finalStage`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem BufIn.of_newBuf {s t : MachineState} {p : Word} {m : Nat} (h : NewBuf s t p m 8)
    (hm : 0 < m) : BufIn s t p m := by
  simp only [NewBuf] at h
  rcases h.2 with h0 | h0
  · omega
  · exact ⟨h.1, h0.2, Or.inr h0.1⟩

theorem BufIn.shrink {s t : MachineState} {p : Word} {m k : Nat} (h : BufIn s t p m)
    (hk : k ≤ m) : BufIn s t p k := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by omega, h3.imp (fun h ↦ by omega) id⟩

theorem BufIn.mono {s t t' : MachineState} {p : Word} {m : Nat} (h : BufIn s t p m)
    (hm : heapNext t ≤ heapNext t') : BufIn s t' p m :=
  ⟨h.1, by have := h.2.1; omega, h.2.2⟩

theorem Apart.shrink {a b : Word} {n m n' m' : Nat} (h : Apart a n b m) (hn : n' ≤ n)
    (hm : m' ≤ m) : Apart a n' b m' := by
  simp only [Apart] at h ⊢
  omega

theorem tables_pos : 0 < tables.length := by decide

/-- What the block writes: the result and `S - [608, 560)`. -/
def FinW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 120 ∨ Within a (s.getReg .x2 - 608) 48

/-- The result's words after the block, from the frame's and the registers' at `h`. -/
structure FinOut (s h t : MachineState) : Prop where
  w0 : t.getMem (s.getReg .x10) = h.getMem (s.getReg .x2 - 840)
  w8 : t.getMem (s.getReg .x10 + 8) = h.getMem (s.getReg .x2 - 832)
  w16 : t.getMem (s.getReg .x10 + 16) = h.getMem (s.getReg .x2 - 824)
  w24 : t.getMem (s.getReg .x10 + 24) = h.getMem (s.getReg .x2 - 768)
  w32 : t.getMem (s.getReg .x10 + 32) = h.getMem (s.getReg .x2 - 760)
  w40 : t.getMem (s.getReg .x10 + 40) = h.getMem (s.getReg .x2 - 752)
  w48 : t.getMem (s.getReg .x10 + 48) = h.getMem (s.getReg .x2 - 1320)
  w56 : t.getMem (s.getReg .x10 + 56) = h.getReg .x27
  w64 : t.getMem (s.getReg .x10 + 64) = h.getMem (s.getReg .x2 - 1144)
  w72 : t.getMem (s.getReg .x10 + 72) = h.getMem (s.getReg .x2 - 1328)
  w80 : t.getMem (s.getReg .x10 + 80) = h.getMem (s.getReg .x2 - 1224)
  w88 : t.getMem (s.getReg .x10 + 88) = h.getReg .x25
  w96 : t.getMem (s.getReg .x10 + 96) = h.getMem (s.getReg .x2 - 632)
  w104 : t.getMem (s.getReg .x10 + 104) = h.getMem (s.getReg .x2 - 624)
  w112 : t.getMem (s.getReg .x10 + 112) = h.getMem (s.getReg .x2 - 616)

set_option maxRecDepth 8192 in
/-- The block at `0x80007c2c` and the epilogue. -/
theorem finalRun {s h : MachineState} (hpre : BusBalancePre s) (I : Inv s h)
    (hout' : h.getMem (s.getReg .x2 - 1312) = s.getReg .x10) (hpc : h.pc = 0x80007c2c) :
    ∃ t, Reaches Image.code h t ∧ Exit s t ∧ FinOut s h t ∧ DFrame h t (FinW s) ∧
      heapNext t = heapNext h := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have spv : h.getReg .x2 = s.getReg .x2 - 1344 := I.sp
  have rd (j : Nat) (hj : j + 8 ≤ 1344) : h.getMem (h.getReg .x2 + BitVec.ofNat 64 j) =
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 (1344 - j)) :=
    congrArg h.getMem (by rw [spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj])
  have hout : h.getMem (h.getReg .x2 + 32) = s.getReg .x10 := (rd 32 (by omega)).trans hout'
  have ho := hpre.out
  have ho2 := ho.2
  have hoM := ho.1
  simp only [Mapped] at hoM
  have hos := hpre.outStack
  rw [stackLo_eq, stack_eq] at hos
  have hof := hpre.outFree
  obtain ⟨u₁, hr₁, hh⟩ := Sym.BlockSpec.reaches b80007c2c_spec hpc (by
    rv_eval [spv, hout, hout']
    and_intros <;> first
      | valid_access hval [hb1]
      | exact Region.valid ho (by addr_omega [hoM]) (by addr_omega [hoM]) (by addr_omega [hoM, ho2])
      | addr_omega [hos, hoM, hb1])
  have fr : DFrame h u₁ (FinW s) := fun a ha ↦ hh.frame a (by
    rv_eval [spv, hout, hout']
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]
      first | exact Or.inl (by addr_omega [hoM]) | exact Or.inr (by addr_omega [hb1])))
  have hn : heapNext u₁ = heapNext h := by
    simp only [heapNext]
    rw [fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hof.2, hw, hi]
      · addr_omega [hw, hi, hb1]]
  have I₁ : Inv s u₁ := I.step hpre fr (fun a ha ↦ by
      rcases ha with ha | ha
      · exact ⟨Or.inl ha, by addr_omega [ha, hos, hb1]⟩
      · exact ⟨Or.inr (Or.inr (Or.inl (by rw [stackLo_eq, stack_eq]; addr_omega [ha, hb1]))),
          by addr_omega [ha, hb1]⟩)
    ⟨hn ▸ I.heap.lo, hn ▸ I.heap.hi⟩ hn.ge (b80007c2c_keeps hh .x2 (by decide))
  obtain ⟨t, hr, ex, hm⟩ := exit hpre I₁ (b80007c2c_pc hh)
  have m (x : Word) : t.getMem x = u₁.getMem x := hm x
  have hnt : heapNext t = heapNext u₁ := by simp only [heapNext, hm]
  refine ⟨t, hr₁.trans hr, ex, ⟨(m _).trans (by have := b80007c2c_m11 hh; rw [hout] at this; exact this.trans (rd 504 (by omega))),
    (m _).trans (by have := b80007c2c_m10 hh; rw [hout] at this; exact this.trans (rd 512 (by omega))),
    (m _).trans (by have := b80007c2c_m9 hh; rw [hout] at this; exact this.trans (rd 520 (by omega))),
    (m _).trans (by have := b80007c2c_m8 hh; rw [hout] at this; exact this.trans (rd 576 (by omega))),
    (m _).trans (by have := b80007c2c_m7 hh; rw [hout] at this; exact this.trans (rd 584 (by omega))),
    (m _).trans (by have := b80007c2c_m6 hh; rw [hout] at this; exact this.trans (rd 592 (by omega))),
    (m _).trans (by have := b80007c2c_m5 hh; rw [hout] at this; exact this.trans (rd 24 (by omega))),
    (m _).trans (by have := b80007c2c_m4 hh; rw [hout] at this; exact this),
    (m _).trans (by have := b80007c2c_m3 hh; rw [hout] at this; exact this.trans (rd 200 (by omega))),
    (m _).trans (by have := b80007c2c_m2 hh; rw [hout] at this; exact this.trans (rd 16 (by omega))),
    (m _).trans (by have := b80007c2c_m1 hh; rw [hout] at this; exact this.trans (rd 120 (by omega))),
    (m _).trans (by have := b80007c2c_m0 hh; rw [hout] at this; exact this),
    (m _).trans (by have := b80007c2c_m14 hh; rw [hout] at this; exact this.trans (rd 712 (by omega))),
    (m _).trans (by have := b80007c2c_m13 hh; rw [hout] at this; exact this.trans (rd 720 (by omega))),
    (m _).trans (by have := b80007c2c_m12 hh; rw [hout] at this; exact this.trans (rd 728 (by omega)))⟩,
    fr.trans (DFrame.of_same hm _) (fun _ h ↦ h), hnt.trans hn⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
