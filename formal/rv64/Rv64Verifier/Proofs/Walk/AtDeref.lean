import Rv64Verifier.Proofs.Walk.R8H

/-!
# `walk`: `tables()` at DEREF's first instruction

The state `setStage` ends in: the call `col(8, 0)` into `sp + 2432` at its entry `0x80004b34`,
returning to `0x80002308`; the KECCAK, XOR, MUL and SET tables finished (`L4 s setT`), all they
reach below `heapNext`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4

/-- At DEREF's `col(8, 0)` call (`0x80004b34`, returning to `0x80002308`). -/
structure AtDeref (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (Bb : Word) : Prop where
  pc : u.pc = 0x80004b34
  m : M8 OI s u A k R Q B Bb (heapNext u) (L4 s setT)
  rd : RD s u
  x10 : u.getReg .x10 = s.getReg .x2 - 224
  x11 : u.getReg .x11 = 8
  x12 : u.getReg .x12 = 0
  x1 : u.getReg .x1 = 0x80002308

set_option maxRecDepth 8192 in
/-- SET's stage ends at DEREF's start. -/
theorem setStage_atDeref (hSS : Rv64Verifier.Layout.StateStepSpec) (hAS : AllocSpec)
    (hC : Rv64Verifier.Layout.ColSpec) (hT : Rv64Verifier.Layout.TermSpec)
    (hBC : Rv64Verifier.Layout.BytecodeSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    (hK : Rv64Verifier.Layout.MemoryColsSpec) (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W (L3 s)) (r : R8 u) (he : EmptyAt u (s.getReg .x2 - 928))
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x1 : u.getReg .x1 = 0x80002100)
    (hpc : u.pc = 0x80004a90) :
    ∃ t, Reaches Image.code u t ∧ (AtDeref OI s t A k R Q B Bb ∨ Dead Image.code t) := by
  obtain ⟨t, r, ⟨p, M, D, a10, a11, a12, a1⟩ | d⟩ :=
    setStage hSS hAS hC hT hBC hP hK hFE hpre h r he x10 x1 hpc
  · exact ⟨t, r, Or.inl ⟨p, M, D, a10, a11, a12, a1⟩⟩
  · exact ⟨t, r, Or.inr d⟩

end Rv64Verifier.Proofs.Walk
