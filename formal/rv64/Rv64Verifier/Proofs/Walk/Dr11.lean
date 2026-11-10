import Rv64Verifier.Proofs.Walk.Dr10

/-!
# `walk`: `tables()`, the DEREF `Table` (R8)

From `AtDeref` to `AtJump`: `derefSums`, `derefHead1`, `derefHead2`, `derefMem`, `derefTail`; the
`Flushes` built is `flushes_deref()`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4

set_option maxRecDepth 8192 in
/-- **DEREF**: from its first `col` call to JUMP's first `prod` call; the DEREF `Table` at `sp + 2144`
joins the finished ones. -/
theorem derefStage (hC : Rv64Verifier.Layout.ColSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec) (hSS : Rv64Verifier.Layout.StateStepSpec) (hAS : AllocSpec)
    (hBC : Rv64Verifier.Layout.BytecodeSpec) (hK : Rv64Verifier.Layout.MemoryColsSpec)
    (hM : Rv64Verifier.Layout.MemorySpec) (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} (hpre : WalkPre s)
    (h : AtDeref OI s u A k R Q B Bb) :
    ∃ t, Reaches Image.code u t ∧ (AtJump OI s t A k R Q B Bb ∨ Dead Image.code t) := by
  obtain ⟨t₁, q₁, ⟨pc₁, D₁, r₁, x10₁, x1₁⟩ | d⟩ := derefSums hC hP hA hpre h
  swap
  · exact ⟨t₁, q₁, Or.inr d⟩
  obtain ⟨t₂, q₂, ⟨pc₂, P, hal, hP₂, D₂, pd₂, H₂, r₂, x22₂⟩ | d⟩ :=
    derefHead1 hSS hAS hC hpre D₁ D₁.hlo₂ r₁ x10₁ x1₁ pc₁
  swap
  · exact ⟨t₂, q₁.trans q₂, Or.inr d⟩
  obtain ⟨t₃, q₃, ⟨pc₃, M₃, F₃, H₃, hH₃, r₃, x21₃, ks₃⟩ | d⟩ :=
    derefHead2 hC hBC hpre hal hP₂ D₁.hlo₂ D₂ pd₂ H₂ r₂ pc₂
  swap
  · exact ⟨t₃, q₁.trans (q₂.trans q₃), Or.inr d⟩
  obtain ⟨t₄, q₄, ⟨pc₄, M₄, F₄, hH₄, r₄, x19₄, ks₄⟩ | d⟩ := derefMem hP hK hM hpre D₁.hlo₂ M₃ F₃ H₃ hH₃ r₃ pc₃
  swap
  · exact ⟨t₄, q₁.trans (q₂.trans (q₃.trans q₄)), Or.inr d⟩
  obtain ⟨t₅, q₅, hj⟩ := derefTail hP hK hFE hpre D₁.hlo₂ M₄ F₄ hH₄ r₄ x19₄
    (by rw [ks₄ .x21 (by decide)]; exact x21₃)
    (by rw [ks₄ .x22 (by decide), ks₃ .x22 (by decide)]; exact x22₂) pc₄
  exact ⟨t₅, q₁.trans (q₂.trans (q₃.trans (q₄.trans q₅))), hj⟩

end Rv64Verifier.Proofs.Walk
