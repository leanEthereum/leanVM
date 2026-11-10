import Rv64Verifier.Proofs.Walk.Dr11
import Rv64Verifier.Proofs.Walk.Jp7
import Rv64Verifier.Proofs.Walk.R9D

/-!
# `walk`: `tables()` from SET's `state_step` to `AtR10` (R8, R9)

`derefStage`, `jumpStage` and `r9` chained (`derefToR10`), and from SET's `state_step` call on
(`setToR10`, with `setStage_atDeref`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4

set_option maxRecDepth 8192 in
/-- From DEREF's first `col` call to `0x80002e40`: the DEREF and JUMP `Table`s built, all six copied
into the tables' buffer. -/
theorem derefToR10 (hC : Rv64Verifier.Layout.ColSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec) (hSS : Rv64Verifier.Layout.StateStepSpec)
    (hSD : Rv64Verifier.Layout.StateDerivedSpec) (hAS : AllocSpec) (hT : Rv64Verifier.Layout.TermSpec)
    (hBC : Rv64Verifier.Layout.BytecodeSpec) (hK : Rv64Verifier.Layout.MemoryColsSpec)
    (hM : Rv64Verifier.Layout.MemorySpec) (hFE : MultilinearContracts.FromElemSpec)
    (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} (hpre : WalkPre s)
    (h : AtDeref OI s u A k R Q B Bb) :
    ∃ t, Reaches Image.code u t ∧ (AtR10 OI s t A k R Q Bb ∨ Dead Image.code t) := by
  obtain ⟨t₁, q₁, h₁ | d⟩ := derefStage hC hP hA hSS hAS hBC hK hM hFE hpre h
  swap
  · exact ⟨t₁, q₁, Or.inr d⟩
  obtain ⟨t₂, q₂, h₂ | d⟩ := jumpStage hP hC hA hSD hAS hT hBC hK hFE hpre h₁
  swap
  · exact ⟨t₂, q₁.trans q₂, Or.inr d⟩
  obtain ⟨t₃, q₃, h₃⟩ := r9 hMC hpre h₂
  exact ⟨t₃, q₁.trans (q₂.trans q₃), h₃⟩

set_option maxRecDepth 8192 in
/-- From SET's `state_step` call (`mulStage`'s end) to `0x80002e40`. -/
theorem setToR10 (hC : Rv64Verifier.Layout.ColSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec) (hSS : Rv64Verifier.Layout.StateStepSpec)
    (hSD : Rv64Verifier.Layout.StateDerivedSpec) (hAS : AllocSpec) (hT : Rv64Verifier.Layout.TermSpec)
    (hBC : Rv64Verifier.Layout.BytecodeSpec) (hK : Rv64Verifier.Layout.MemoryColsSpec)
    (hM : Rv64Verifier.Layout.MemorySpec) (hFE : MultilinearContracts.FromElemSpec)
    (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W (L3 s)) (r : R8 u) (he : EmptyAt u (s.getReg .x2 - 928))
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x1 : u.getReg .x1 = 0x80002100)
    (hpc : u.pc = 0x80004a90) :
    ∃ t, Reaches Image.code u t ∧ (AtR10 OI s t A k R Q Bb ∨ Dead Image.code t) := by
  obtain ⟨t₁, q₁, h₁ | d⟩ := setStage_atDeref hSS hAS hC hT hBC hP hK hFE hpre h r he x10 x1 hpc
  swap
  · exact ⟨t₁, q₁, Or.inr d⟩
  obtain ⟨t₂, q₂, h₂⟩ := derefToR10 hC hP hA hSS hSD hAS hT hBC hK hM hFE hMC hpre h₁
  exact ⟨t₂, q₁.trans q₂, h₂⟩

end Rv64Verifier.Proofs.Walk
