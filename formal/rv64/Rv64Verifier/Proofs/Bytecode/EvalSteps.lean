import Rv64Verifier.Proofs.Bytecode.Bits
import Rv64Verifier.Proofs.Runtime.Inv

/-!
# `Bytecode::evaluate`: its two halfword loads

`lhu t2, 0(t0)` at `0x80011114` (a position) and `lhu a6, 0(a0)` at `0x800113c8` (a bucket) load
from `u16` arrays at any even address, which the executor reads only from an 8-aligned base: each
is one `step_lhu`, and the bounds check after it a one-instruction block checked against a hand
written `Expect` (`branchExpect`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 Rv64Verifier.Runtime

/-- Every register, unchanged. -/
def idRegs : List (Reg × Sym.E) :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31].map
    fun r ↦ (r, .reg r)

/-- A conditional branch: one step, nothing else. -/
def branchExpect (op : Sym.CmpOp) (a b : Reg) (taken fall : Word) : Sym.Expect where
  steps := 1
  pc := .ite op (.reg a) (.reg b) (.c taken) (.c fall)
  regs := idRegs
  mem := []
  writes := []
  obl := []

/-- `bgeu t2, s2` at `0x80011118`. -/
theorem br11118 : Spec 0x80011118 (branchExpect .geu .x7 .x18 0x80011748 0x8001111c) :=
  spec_of 17478 1 (by decide +kernel) (by decide) (by decide) (by decide)

/-- `bgeu a6, s5` at `0x800113cc`. -/
theorem br113cc : Spec 0x800113cc (branchExpect .geu .x16 .x21 0x80011748 0x800113d0) :=
  spec_of 17651 1 (by decide +kernel) (by decide) (by decide) (by decide)

theorem branch_regs {op : Sym.CmpOp} {a b : Reg} {x y : Word} {s t : MachineState}
    (h : (branchExpect op a b x y).Holds s t) : ∀ r, t.getReg r = s.getReg r := by
  intro r
  cases r with
  | x0 => simp [MachineState.getReg]
  | _ => exact h.reg _ rfl

theorem branch_mem {op : Sym.CmpOp} {a b : Reg} {x y : Word} {s t : MachineState}
    (h : (branchExpect op a b x y).Holds s t) : ∀ a, t.getMem a = s.getMem a :=
  fun c ↦ h.frame c fun _ hk ↦ by cases hk

theorem branch_pc {a b : Reg} {x y : Word} {s t : MachineState}
    (h : (branchExpect .geu a b x y).Holds s t) :
    t.pc = if (s.getReg b).toNat ≤ (s.getReg a).toNat then x else y := by
  have hc : (!BitVec.ult (s.getReg a) (s.getReg b)) =
      decide ((s.getReg b).toNat ≤ (s.getReg a).toNat) := by
    simp only [BitVec.ult]
    by_cases h : (s.getReg b).toNat ≤ (s.getReg a).toNat
    · simp [h]
    · simp [h]; omega
  rw [h.pc]
  simp only [branchExpect, Sym.E.eval, Sym.CmpOp.eval, hc, decide_eq_true_eq]

/-- `lhu rd, 0(rs)` then `bgeu rd, rb`: `rd` holds the halfword, the bounds check decides the
pc, nothing else changes. -/
theorem lhu_bgeu {pc : Word} {rd rs rb : Reg} {taken fall : Word} {s : MachineState}
    (hpc : s.pc = pc)
    (hf : Image.code.fetch pc = some (.base (.LHU rd rs 0)))
    {pc4 : Word} (h4 : pc + 4 = pc4) (hbr : Spec pc4 (branchExpect .geu rd rb taken fall))
    (hrd : rd ≠ .x0) (hrb : rb ≠ rd)
    (hv : Sym.validAccess 2 (s.getReg rs) = true) :
    ∃ t, Reaches Image.code s t ∧
      t.getReg rd = (s.getHalfword (s.getReg rs)).zeroExtend 64 ∧
      (∀ r, r ≠ rd → t.getReg r = s.getReg r) ∧ (∀ a, t.getMem a = s.getMem a) ∧
      t.pc = if (s.getReg rb).toNat ≤ ((s.getHalfword (s.getReg rs)).zeroExtend 64 : Word).toNat
        then taken else fall := by
  have hoff : s.getReg rs + signExtend12 0 = s.getReg rs := by
    simp [signExtend12]
  obtain ⟨u, hu, hpc', hr, hm⟩ := step_lhu (rd := rd) (rs1 := rs) (off := 0) (by rw [hpc]; exact hf)
    (by rw [hoff]; exact hv)
  rw [hoff] at hr
  have hur : ∀ r, u.getReg r = if r = rd then (s.getHalfword (s.getReg rs)).zeroExtend 64
      else s.getReg r := by
    intro r
    rw [hr r]
    by_cases h : r = rd
    · simp [h, hrd]
    · simp [h]
  obtain ⟨t, ht, h⟩ := hbr u (by rw [hpc', hpc, h4]) trivial
  have hreg := branch_regs h
  refine ⟨t, (show Reaches Image.code s u from ⟨1, hu⟩).trans ⟨_, ht⟩, ?_, fun r hne ↦ ?_,
    fun a ↦ ?_, ?_⟩
  · rw [hreg, hur]; simp
  · rw [hreg, hur]; simp [hne]
  · rw [branch_mem h, hm]
  · rw [branch_pc h, hur, hur]; simp [hrb]

end Rv64Verifier.Proofs.Bytecode.Eval
