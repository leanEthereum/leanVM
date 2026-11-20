/-
  Rv64mc.Proof.Runtime.InputWord

  `Input::word` meets `InputWordSpec`: it reads the slice's length, halts on zero, else returns the word at the
  slice's pointer and stores the pointer advanced by a word and the length less one.
-/

import Rv64mc.Gen.Tmpl.VerifierRv64.Input.Word
import Rv64mc.Spec.Runtime.Input
import Rv64mc.Spec.Runtime.Panic

namespace Rv64mc.Proof.Runtime.InputWord

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.VerifierRv64.Input.Word (Link tmpl)

theorem inputPtrAt_eq (a : Word) : inputPtrAt a = a := by
  simp only [inputPtrAt, Layouts.Input.f0, Layouts.SliceE.ptr]; exact BitVec.add_zero a

theorem inputLenAt_eq (a : Word) : inputLenAt a = a + 8#64 := rfl

theorem ne_add8 (a : Word) : a ≠ a + 8#64 := fun h => by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 by decide] at this
  have := a.isLt
  omega

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat}

/-- **The contract of `Input::word`**, with no stack, from `halt`'s. -/
theorem ok (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p) (hhalt : NoReturn env p L.halt.idx 0) :
    InputWordSpec env p i 0 := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, ⟨hlo, hhi⟩, hal⟩ hk
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hL.halt, hL.s0, Holds.post] using [hhalt.contract]
  -- `halt`'s precondition
  · exact Holds.pre_call (by show _ ≤ (regs .x2).toNat; rw [hsp]; exact hstk) hst hnx trivial
      (by show (regs .x2).toNat % 16 = 0; rw [hsp]; exact hal)
  -- the return
  · have hlay := env.layout
    simp only [Layouts.Input.byteSize] at hhi
    have h8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
    have hn0 : regs .x10 ≠ env.nextAddr := fun h => by rw [h] at hlo; omega
    have hn8 : regs .x10 + 8#64 ≠ env.nextAddr := fun h => by rw [← BitVec.toNat_inj, h8] at h; omega
    have hs0 : (regs .x10).toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ (regs .x10).toNat := by omega
    have hs8 : (regs .x10 + 8#64).toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ (regs .x10 + 8#64).toNat := by
      omega
    have hf1 := Env.Frame.setMem_out (top := top) (out := WordOut regs m)
      (v := m.getMem (regs .x10) + 8#64) hnx (Or.inl (inputPtrAt_eq _).symm) hn0
    have hnx1 : (env.next (m.setMem (regs .x10) (m.getMem (regs .x10) + 8#64))).toNat ≤ env.heapEnd.toNat :=
      hf1.2.1
    have hf2 := Env.Frame.setMem_out (top := top) (out := WordOut regs m)
      (v := m.getMem (regs .x10 + 8#64) + 18446744073709551615#64) hnx1 (Or.inr (inputLenAt_eq _).symm) hn8
    apply hk
    refine ⟨by simp (disch := decide) only [AbiRegs.updReg_iff]; exact AbiRegs.refl hsp,
      hf1.trans hf2 (Nat.le_refl _) fun a h => Or.inr (Or.inr (Or.inr h)),
      Env.static_setMem (Env.static_setMem hst hs0) hs8, ?_, ?_, ?_, ?_⟩
    · show m.getMem (inputLenAt (regs .x10)) ≠ 0; rw [inputLenAt_eq]; exact hc
    · show m.getMem (m.getMem (regs .x10)) = m.getMem (m.getMem (inputPtrAt (regs .x10)))
      rw [inputPtrAt_eq]
    · rw [inputPtrAt_eq]
      simp [MachineState.getMem, MachineState.setMem, ne_add8 (regs .x10)]
    · rw [inputLenAt_eq, BitVec.sub_eq_add_neg]
      simp [MachineState.getMem, MachineState.setMem]

end Rv64mc.Proof.Runtime.InputWord
