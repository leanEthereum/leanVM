import Rv64Verifier.Proofs.Bytecode.EvalEnv
import Rv64Verifier.Blocks.F84

/-!
# `Bytecode::evaluate`: the ways out

`0x8001170c` restores the saved registers and returns (`epilogue`); `0x800116dc` writes
`Err(MultilinearSize)` (`err_exit`); `0x800116f8` writes `Ok(total)` from `t0`, `a7`, `a6`
(`ok_exit`), its slot's address read back from `sp + 8`.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `sp` as numbers, from the stack's validity. -/
theorem sp_bounds {s : MachineState} (h : RtStack s evalStack) :
    heapEnd + evalStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have hb := h.bounds (by decide) (by decide)
  have ha := h.above
  simp only [stackLo, BitVec.toNat_sub, BitVec.toNat_ofNat] at ha
  have := (s.getReg .x2).isLt
  simp only [evalStack, eqKernelStack, mulStack, heapEnd] at hb ha ⊢
  omega

/-- The epilogue: the saved registers back, `sp` up, return; memory unchanged. -/
theorem epilogue {s t : MachineState} (hpc : t.pc = 0x8001170c) (hs : Saved s t)
    (hst : RtStack s evalStack) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧
      ∀ a, u.getMem a = t.getMem a := by
  have hsp := sp_bounds hst
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b8001170c_spec hpc (by
    rv_eval [hs.sp, fp]
    and_intros <;> valid_access hst.valid [hsp])
  have e (r : Reg) (hr : (b8001170c.regs.find? fun p ↦ Sym.Reg.beqN p.1 r).isSome = true) :=
    h.reg r hr
  have x1 := e .x1 rfl
  have x2 := e .x2 rfl
  have x8 := e .x8 rfl
  have x9 := e .x9 rfl
  have x18 := e .x18 rfl
  have x19 := e .x19 rfl
  have x20 := e .x20 rfl
  have x21 := e .x21 rfl
  have x22 := e .x22 rfl
  have x23 := e .x23 rfl
  have x24 := e .x24 rfl
  have x25 := e .x25 rfl
  have x26 := e .x26 rfl
  have x27 := e .x27 rfl
  have pc := h.pc
  rv_eval [hs.sp, fp, hs.r1, hs.r8, hs.r9, hs.r18, hs.r19, hs.r20, hs.r21, hs.r22, hs.r23, hs.r24,
    hs.r25, hs.r26, hs.r27] at x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 pc
  refine ⟨u, hr, by rw [pc, returnAddress_eq], ?_, b8001170c_mem_same h⟩
  exact preserves_of x2 x8 x9 x18 x19 (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)

/-- `Err(MultilinearSize)`: tag `1` at `a0`, then the epilogue. -/
theorem err_exit {s t : MachineState} (hpc : t.pc = 0x800116dc) (hs : Saved s t)
    (hst : RtStack s evalStack) (h10 : t.getReg .x10 = s.getReg .x10)
    (hout : ValidMemRange (s.getReg .x10) 4)
    (hap : Apart (s.getReg .x10) 32 (stackLo s evalStack) evalStack) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧
      u.getMem (s.getReg .x10) = 1 ∧
      ∀ a, ¬ Within a (s.getReg .x10) 32 → u.getMem a = t.getMem a := by
  have hb := ValidMemRange.bounds hout (by decide)
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b800116dc_spec hpc (by
    rv_eval [h10]
    and_intros <;> valid_access hout [hb])
  have m0 := b800116dc_m_x10_0 h
  rw [h10] at m0
  have hfr := b800116dc_frame h (by rw [h10]; omega)
  rw [h10] at hfr
  have hsp := sp_bounds hst
  have hs' : Saved s u := hs.of_frame ((b800116dc_keeps h) .x2 (by decide))
    (fun a h1 h2 ↦ hfr a (by addr_omega [h1, h2, hb, hap, hsp])) (by addr_omega [hsp])
  obtain ⟨v, hrv, hvpc, hpres, hvm⟩ := epilogue (b800116dc_pc h) hs' hst
  refine ⟨v, hr.trans hrv, hvpc, hpres, by rw [hvm, m0], fun a ha ↦ ?_⟩
  rw [hvm, hfr a (by addr_omega [ha])]

/-- `Ok(total)`, the total's limbs in `t0`, `a7`, `a6`: tag `0` at `a0`, then the epilogue. -/
theorem ok_exit {s t : MachineState} (hpc : t.pc = 0x800116f8) (hs : Saved s t)
    (hs8 : t.getMem (s.getReg .x2 - 1960) = s.getReg .x10) (hst : RtStack s evalStack)
    (hout : ValidMemRange (s.getReg .x10) 4)
    (hap : Apart (s.getReg .x10) 32 (stackLo s evalStack) evalStack) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧
      u.getMem (s.getReg .x10) = 0 ∧ u.getMem (s.getReg .x10 + 8) = t.getReg .x5 ∧
      u.getMem (s.getReg .x10 + 16) = t.getReg .x17 ∧ u.getMem (s.getReg .x10 + 24) = t.getReg .x16 ∧
      ∀ a, ¬ Within a (s.getReg .x10) 32 → u.getMem a = t.getMem a := by
  have hb := ValidMemRange.bounds hout (by decide)
  have hsp := sp_bounds hst
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b800116f8_spec hpc (by
    rv_eval [hs.sp, fp, hs8]
    and_intros <;> first | valid_access hout [hb] | valid_access hst.valid [hsp])
  have m0 := b800116f8_m0 h
  have m1 := b800116f8_m1 h
  have m2 := b800116f8_m2 h
  have m3 := b800116f8_m3 h
  rv_eval [hs.sp, fp, hs8] at m0 m1 m2 m3
  have hfr : ∀ a, ¬ Within a (s.getReg .x10) 32 → u.getMem a = t.getMem a := fun a ha ↦
    h.frame a (by rv_eval [hs.sp, fp, hs8]; and_intros <;> addr_omega [ha, hb])
  have hs' : Saved s u := hs.of_frame ((b800116f8_keeps h) .x2 (by decide))
    (fun a h1 h2 ↦ hfr a (by addr_omega [h1, h2, hb, hap, hsp])) (by addr_omega [hsp])
  obtain ⟨v, hrv, hvpc, hpres, hvm⟩ := epilogue (b800116f8_pc h) hs' hst
  refine ⟨v, hr.trans hrv, hvpc, hpres, by rw [hvm, m3], by rw [hvm, m2], by rw [hvm, m1],
    by rw [hvm, m0], fun a ha ↦ ?_⟩
  rw [hvm, hfr a ha]

end Rv64Verifier.Proofs.Bytecode.Eval
