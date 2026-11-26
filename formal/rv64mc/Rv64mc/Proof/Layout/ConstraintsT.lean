/-
  Rv64mc.Proof.Layout.ConstraintsT

  `Table::constraints(columns)` is total: for the jump table's opcode (`4`) it tail-calls `jump_constraints` on the
  columns (`JumpConstraintsT`), for any other it stores the empty vector at `sret`. Its result is a vector's
  (`VecReprT.VecT`), empty or of two elements in a fresh buffer; the run ends with the guest's abort (`AbortStop`)
  where `jump_constraints` does.

  The precondition: `JumpConstraintsT.PreT` (`sret` a caller's, in a window, aligned; the columns `SliceT`), with the
  opcode in `a1` and the columns in `(a2, a3)`.

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.JumpConstraintsT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Table.Constraints

namespace Rv64mc.Proof.Layout.ConstraintsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT)
open Rv64mc.Proof.Keccak.TryFromFnT (SliceT)
open Rv64mc.Gen.Verifier.Layout.Table.Constraints (Link tmpl)

/-- The total precondition: `sret` a caller's (`SretPre`), in a window, aligned; the columns `(a2, a3)`
    `SliceT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    SliceT env (regs .x12) (regs .x13).toNat

/-- The total postcondition: the result a vector's (`VecT`), empty, or of two elements in a fresh buffer. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ ((vecLen m' (regs .x10)).toNat = 0 ∨
    ((vecLen m' (regs .x10)).toNat = 2 ∧ env.Fresh m m' (vecPtr m' (regs .x10)) 32))

/-- **The total contract of `Table::constraints`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

set_option rv_sym.heap true in
/-- **`Table::constraints` is total**, with no stack beyond `jump_constraints`'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need : Nat} (hjc : JumpConstraintsT.SpecT env p L.jumpConstraints.idx need) : SpecT env p i need := by
  rv_autoT hp with [hL] using [hjc]
  all_goals try
    have h0 : ((((m.setMem (regs .x10) 0#64).setMem (regs .x10 + 8#64) 8#64).setMem (regs .x10 + 16#64)
        0#64).getMem (rvCapAt (regs .x10))) = 0#64 := by
      simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]
      rw [MachineState.getMem_setMem_ne (Ne.symm (Tactic.add_ne (by decide))),
        MachineState.getMem_setMem_ne (Ne.symm (Tactic.add_ne (by decide))), MachineState.getMem_setMem_eq]
    rw [h0]
  · exact .inl rfl
  · decide
  · have h := hret1_21
    rw [Runtime.ReserveT.vecLen_eq, Runtime.ReserveT.vecCap_eq] at h
    exact h
  · exact .inr ⟨hret1_22, hret1_23⟩

end Rv64mc.Proof.Layout.ConstraintsT

/-- info: 'Rv64mc.Proof.Layout.ConstraintsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.ConstraintsT.total
