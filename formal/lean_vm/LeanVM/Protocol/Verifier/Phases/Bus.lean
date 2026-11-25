/-
  LeanVM.Protocol.Verifier.Phases.Bus

  The bus phase `verifyBusBalance` split along its sub-programs.
-/

module

public import LeanVM.Protocol.Verifier.Phases
import LeanVM.Protocol.Compile.Prog

/-!
# The bus, split

`verifyBusBalance` (step 3 of `verify_execution`, `crates/verifier/src/bus.rs`) in normal form
(`verifyBusBalance_eq`): its depth's check, the grind, the slot weights and `β`, the GKR walk and
its count root's check, the framework's reads, the bytecode's share and the check `ev` of the fixed
polynomial's value, then the pure tail `busOf` (the framework's claims, the fingerprints and the
leaf decomposition of the three sides). The proofs about the phase rewrite with it and read
`busOf`, so a change to what the bus computes after its last message changes `busOf` alone.

For the guest, whose `verify_sub` runs the parts as separate functions, the same phase is its
depth's check, then `busChallenges`, `gkrPhase` and `busRest` (the reads, then `busOf`), all at the
push side's depth `busDepth` (`verifyBusBalance_split`).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile

@[expose] public section

/-- The push side's bus depth of a layout. -/
abbrev busDepth (layout : Layout) : ℕ :=
  (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth

/-- The bus's grind, its slot weights and `β`. -/
def busChallenges (depth : ℕ) : VerifierProgram (List E × E) :=
  (VerifierProgram.grindProofOfWork (busGrindingBits depth)).bind fun _ ↦
  (VerifierProgram.sampleChallenges (2 ^ busBits)).bind fun weights ↦
  VerifierProgram.sampleChallenge.bind fun beta ↦ VerifierProgram.ret (weights, beta)

/-- The GKR walk and the count root's check (`verify_bus_gkr`). -/
def gkrPhase (depth : ℕ) : VerifierProgram (E × List E × List E) := do
  let r ← verifyGkrGrandProducts depth
  VerifierProgram.require (r.1 ≠ 0)
  return r

/-- **What the bus returns** from what it sampled and read (`bus.rs`, after the last message): the
framework's claims at the GKR point's low coordinates, the bytecode's point, the GKR point, and the
three sides' forms and totals, accumulated over the fingerprints of the slot weights `weights`, the
memory limbs `memory`, the finalize counts `memoryFinal`, `bytecodeFinal` and the bytecode's
share. -/
def busOf (layout : Layout) (weights : List E) (beta : E) (point treeValues memory : List E)
    (memoryFinal bytecodeFinal share : E) (bytecodePoint : List E) : BusResult :=
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1] memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let fp := fingerprints weights memory memoryLow bytecodeLow share
  let pcFinal := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let r1 := accumulateSide forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let r2 := accumulateSide r1.1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let r3 := accumulateSide r2.1 2 layout.count countLayout [] [1] 0 point (treeValues.getD 2 0)
  ⟨claims, bytecodePoint, point, r3.1, [r1.2, r2.2, r3.2]⟩

/-- **The bus in normal form**: its messages, challenges and checks, then `busOf`. -/
theorem verifyBusBalance_eq (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout) :
    verifyBusBalance ev layout = (do
      VerifierProgram.require
        ((busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth < 64)
      VerifierProgram.grindProofOfWork
        (busGrindingBits (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth)
      let weights ← VerifierProgram.sampleChallenges (2 ^ busBits)
      let beta ← VerifierProgram.sampleChallenge
      let g ← verifyGkrGrandProducts
        (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth
      VerifierProgram.require (g.1 ≠ 0)
      let memory ← VerifierProgram.readScalars 2
      let memoryFinal ← VerifierProgram.readScalar
      let bytecodeFinal ← VerifierProgram.readScalar
      let (share, bytecodePoint, value) ← bytecodeShare weights (g.2.1.take layout.logBytecode)
      ev layout.bytecode bytecodePoint value
      return busOf layout weights beta g.2.1 g.2.2 memory memoryFinal bytecodeFinal share
        bytecodePoint) :=
  rfl

/-- `verifyBusBalance` after the GKR walk and its count root's check, from its slot
weights, `β`, point and values: the framework's reads, the bytecode's share and its sumcheck, the
check `ev` of the stacked bytecode at the sumcheck's point, then `busOf`. -/
def busRest (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout)
    (weights : List E) (beta : E) (point treeValues : List E) : VerifierProgram BusResult := do
  let memory ← VerifierProgram.readScalars 2
  let memoryFinal ← VerifierProgram.readScalar
  let bytecodeFinal ← VerifierProgram.readScalar
  let (share, bytecodePoint, value) ← bytecodeShare weights (point.take layout.logBytecode)
  ev layout.bytecode bytecodePoint value
  return busOf layout weights beta point treeValues memory memoryFinal bytecodeFinal share
    bytecodePoint

/-- `verifyBusBalance` as the depth's check, `busChallenges`, `gkrPhase` and `busRest`. -/
theorem verifyBusBalance_split (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout) :
    verifyBusBalance ev layout =
      (VerifierProgram.require (busDepth layout < 64)).bind fun _ ↦
      (busChallenges (busDepth layout)).bind fun wb ↦
      (gkrPhase (busDepth layout)).bind fun r ↦
        busRest ev layout wb.1 wb.2 r.2.1 r.2.2 := by
  rw [verifyBusBalance_eq]
  simp only [busChallenges, gkrPhase, busRest, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

end
end LeanVM.Protocol.Verifier
