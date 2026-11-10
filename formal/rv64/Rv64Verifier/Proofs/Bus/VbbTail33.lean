import Rv64Verifier.Proofs.Bus.VbbTail32

/-!
# `verify_bus_balance`'s side loop: the side's tuple read

The block at `0x800074e0` reads side `i`'s tuple into `s0`, `s1`, `s2`, `s3`, `s4`, `s6`, `s10`
and the frame (`At74e0`), then calls `try_allocate_in` for the framework selectors.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Side `i`'s `BusLayout`, in the frame. -/
def layAt (s : MachineState) (i : Nat) : Word := s.getReg .x2 - BitVec.ofNat 64 (1080 - 56 * i)

/-- Past the block at `0x800074e0`. -/
structure At74e0 (s h u : MachineState) (i : Nat) : Prop where
  x1 : u.getReg .x1 = 0x80007554
  x8 : u.getReg .x8 = sideWord s h i 32
  x9 : u.getReg .x9 = h.getMem (layAt s i + 8)
  x10 : u.getReg .x10 = s.getReg .x2 - 248
  x11 : u.getReg .x11 = h.getMem (layAt s i + 16)
  x12 : u.getReg .x12 = 0
  x13 : u.getReg .x13 = 8
  x14 : u.getReg .x14 = 24
  x18 : u.getReg .x18 = sideWord s h i 16
  x19 : u.getReg .x19 = h.getMem (layAt s i + 16)
  x20 : u.getReg .x20 = layAt s i
  x22 : u.getReg .x22 = sideWord s h i 8
  x26 : u.getReg .x26 = sideWord s h i 64
  keeps : ∀ r ∈ ([.x2, .x21, .x23, .x24, .x25, .x27] : List Reg), u.getReg r = h.getReg r
  m176 : u.getMem (s.getReg .x2 - 1168) = sideWord s h i 80
  m184 : u.getMem (s.getReg .x2 - 1160) = sideWord s h i 72
  m96 : u.getMem (s.getReg .x2 - 1248) = sideWord s h i 56
  m80 : u.getMem (s.getReg .x2 - 1264) = sideWord s h i 48
  m152 : u.getMem (s.getReg .x2 - 1192) = sideWord s h i 24
  m192 : u.getMem (s.getReg .x2 - 1152) = BitVec.ofNat 64 i
  frame : DFrame h u fun a ↦ Within a (s.getReg .x2 - 1264) 8 ∨ Within a (s.getReg .x2 - 1248) 8 ∨
    Within a (s.getReg .x2 - 1192) 48

set_option maxRecDepth 8192 in
theorem block74e0 {s h : MachineState} {i : Nat} (hpre : BusBalancePre s) (I : Inv s h)
    (hi : i < 3) (hx22 : h.getReg .x22 = BitVec.ofNat 64 i)
    (hlay : sideWord s h i 40 = layAt s i) (hpc : h.pc = 0x800074e0) :
    ∃ u, Reaches Image.code h u ∧ u.pc = 0x800049ac ∧ At74e0 s h u i := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have spv : h.getReg .x2 = s.getReg .x2 - 1344 := I.sp
  simp only [sideWord, layAt] at hlay ⊢
  interval_cases i <;>
  · rv_eval [Nat.reduceMul, Nat.reduceSub] at hlay
    obtain ⟨u, hr, hh⟩ := Sym.BlockSpec.reaches b800074e0_spec hpc (by
      rv_eval [spv, hx22, hlay]
      and_intros <;> first | valid_access hval [hb1] | addr_omega [hb1])
    have k₁ := b800074e0_keeps hh
    refine ⟨u, hr, b800074e0_pc hh, ⟨b800074e0_x1 hh, ?_, ?_, ?_, ?_, b800074e0_x12 hh,
      b800074e0_x13 hh, b800074e0_x14 hh, ?_, ?_, ?_, ?_, ?_, fun r hr ↦ k₁ r (mem_of_mem hr _),
      ?_, ?_, ?_, ?_, ?_, ?_, fun a ha ↦ hh.frame a ?_⟩⟩
    · rw [b800074e0_x8 hh]; rv_eval [spv, hx22, hlay, sideWord, layAt, Nat.reduceMul, Nat.reduceSub]
    · rw [b800074e0_x9 hh]; rv_eval [spv, hx22, hlay, sideWord, layAt, Nat.reduceMul, Nat.reduceSub]
    · rw [b800074e0_x10 hh]; rv_eval [spv]
    · rw [b800074e0_x11 hh]; rv_eval [spv, hx22, hlay, sideWord, layAt, Nat.reduceMul, Nat.reduceSub]
    · rw [b800074e0_x18 hh]; rv_eval [spv, hx22, hlay, sideWord, layAt, Nat.reduceMul, Nat.reduceSub]
    · rw [b800074e0_x19 hh]; rv_eval [spv, hx22, hlay, sideWord, layAt, Nat.reduceMul, Nat.reduceSub]
    · rw [b800074e0_x20 hh]; rv_eval [spv, hx22, hlay, sideWord, layAt, Nat.reduceMul, Nat.reduceSub]
    · rw [b800074e0_x22 hh]; rv_eval [spv, hx22, hlay, sideWord, layAt, Nat.reduceMul, Nat.reduceSub]
    · rw [b800074e0_x26 hh]; rv_eval [spv, hx22, hlay, sideWord, layAt, Nat.reduceMul, Nat.reduceSub]
    · have e := b800074e0_m_x2_176 hh; rv_eval [spv, hx22, hlay] at e
      rv_eval [sideWord, Nat.reduceMul, Nat.reduceSub]; exact e
    · have e := b800074e0_m_x2_184 hh; rv_eval [spv, hx22, hlay] at e
      rv_eval [sideWord, Nat.reduceMul, Nat.reduceSub]; exact e
    · have e := b800074e0_m_x2_96 hh; rv_eval [spv, hx22, hlay] at e
      rv_eval [sideWord, Nat.reduceMul, Nat.reduceSub]; exact e
    · have e := b800074e0_m_x2_80 hh; rv_eval [spv, hx22, hlay] at e
      rv_eval [sideWord, Nat.reduceMul, Nat.reduceSub]; exact e
    · have e := b800074e0_m_x2_152 hh; rv_eval [spv, hx22, hlay] at e
      rv_eval [sideWord, Nat.reduceMul, Nat.reduceSub]; exact e
    · have e := b800074e0_m_x2_192 hh; rv_eval [spv, hx22, hlay] at e
      rv_eval [sideWord, Nat.reduceMul, Nat.reduceSub]; exact e
    · rv_eval [spv, hx22, hlay]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]
        first
          | exact Or.inl (by addr_omega [hb1])
          | exact Or.inr (Or.inl (by addr_omega [hb1]))
          | exact Or.inr (Or.inr (by addr_omega [hb1])))

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
