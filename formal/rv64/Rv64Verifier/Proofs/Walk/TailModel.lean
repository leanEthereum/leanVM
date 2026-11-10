import Rv64Verifier.Proofs.Walk.AtR17
import Rv64Verifier.Proofs.Pcs.VsoKeeps

/-!
# `walk`'s mirror from the table phase on

`tailRust` in the machine's stages (`tail_tables`, `afterTables`), and `TracksR`'s steps: a bind of
a mirror that keeps the proof and the roots (`Pcs.Keeps`), and the end.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript

/-- What is left once the table sumcheck has returned `evaluations`. -/
def afterTables (publicInput : List (BitVec 8)) (layout : LayoutMirror.LayoutRust)
    (tableRows : List (BitVec 64)) (logInverseRate : BitVec 64) (bus : BusResultRust)
    (evaluations : List (List E × List E)) : TM SummaryRust :=
  (do
    let claims := bus.claims ++ tableClaimsRust evaluations
    let publicClaims ← publicInputRust layout publicInput
    let claims := claims ++ publicClaims
    let (openings, keccakStart, keccakEnd) ← keccakPhaseRust layout evaluations
    let claims := claims ++
      openings.outputs.toList.map fun pw ↦ (⟨LayoutMirror.qkeccakRust, pw.1, pw.2⟩ : ColumnClaim)
    let (ringTarget, ringWeight) ← Pcs.ringSwitchRust openings.inputs.1 openings.inputs.2
    Pcs.verifyStackedOpeningRust layout.stackLog logInverseRate.toNat
      (⟨.placedRing layout.qkeccak ringWeight, ringTarget⟩ :: claims.filterMap (onStackRust layout))
    pure ⟨layout.logMemory, tableRows, logInverseRate.toNat, bus.bytecodePoint,
      (keccakStart, keccakEnd)⟩) >>= finishRust

theorem tail_tables (publicInput : List (BitVec 8)) (layout : LayoutMirror.LayoutRust)
    (tableRows : List (BitVec 64)) (lir : BitVec 64) (bus : BusResultRust) :
    tailRust publicInput layout tableRows lir bus = tablePhaseRust layout bus >>=
      afterTables publicInput layout tableRows lir bus := by
  rw [tailRust, bind_assoc]
  rfl

section TracksR
variable {OI : MachineState → Word → List (List Opening) → Prop} {β : Type}
  {C : TM SummaryRust} {s u v : MachineState} {r : Digest × ℕ × ℕ}

theorem TracksR.keep (h : TracksR OI s u r C)
    (hk : ∀ T, TranscriptAt u (tp s) T → TranscriptAt v (tp s) T) : TracksR OI s v r C :=
  fun proof hp ↦ by
    obtain ⟨T, e, er, hT, hr⟩ := h proof hp
    exact ⟨T, e, er, hk T hT, hr⟩

theorem TracksR.bind {A : TM β} {K : β → TM SummaryRust} {x : β}
    (h : TracksR OI s u r (A >>= K)) (hk : Pcs.Keeps A)
    (hA : ∀ T, TranscriptAt u (tp s) T → ∃ T', A.run T = some (x, T') ∧ TranscriptAt v (tp s) T') :
    TracksR OI s v r (K x) := fun proof hp ↦ by
  obtain ⟨T₁, e₁, r₁, h₁, q₁⟩ := h proof hp
  obtain ⟨T₂, e₂, h₂⟩ := hA T₁ h₁
  obtain ⟨k1, k2, -⟩ := hk T₁ x T₂ e₂
  refine ⟨T₂, k1.trans e₁, k2.trans r₁, h₂, ?_⟩
  rw [q₁, StateT.run_bind, e₂]
  rfl

theorem TracksR.done {d : SummaryRust} (h : TracksR OI s u r (pure d)) :
    ∀ proof, ProofIn OI s (s.getReg .x13) proof →
      ∃ summary, verifyExecutionRust (Proofs.Bytecode.readBytecode s (s.getReg .x11))
        (bytesAt s (s.getReg .x12) 32) proof = some summary := fun proof hp ↦ by
  obtain ⟨T, -, -, -, hr⟩ := h proof hp
  refine ⟨d, ?_⟩
  show ((prog s).run (initT s proof)).map (·.1) = some d
  rw [hr]
  rfl

end TracksR

end Rv64Verifier.Proofs.Walk
