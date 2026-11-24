/-
  LeanVM.Protocol.Verifier.Phases.Bus

  The bus phase `verifyBusBalance` split along its sub-programs.
-/

module

public import LeanVM.Protocol.Verifier.Phases
import LeanVM.Protocol.Compile.Prog

/-!
# The bus, split

`verifyBusBalance` (step 3 of `verify_execution`, `crates/verifier/src/bus.rs`) is its depth's
check, then `busChallenges` (the grind, the slot weights and `β`), `gkrPhase` (the GKR walk and the
count root's check) and `busRest` (the framework's claims, the bytecode's share and the check of
the fixed polynomial's value, the leaf decomposition), all at the push side's depth `busDepth`
(`verifyBusBalance_split`). The guest's `verify_sub` runs the parts as separate functions.
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

/-- `verifyBusBalance` after the GKR walk and its count root's check, from its slot
weights, `β`, point and values: the framework's claims, the bytecode's share and its sumcheck, the
check `ev` of the stacked bytecode at the sumcheck's point, and the leaf decomposition. -/
def busRest (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout)
    (weights : List E) (beta : E) (point treeValues : List E) : VerifierProgram BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← VerifierProgram.readScalars 2
  let memoryFinal ← VerifierProgram.readScalar
  let bytecodeFinal ← VerifierProgram.readScalar
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1] memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let (share, bytecodePoint, value) ← bytecodeShare weights bytecodeLow
  ev layout.bytecode bytecodePoint value
  let fp := fingerprints weights memory memoryLow bytecodeLow share
  let pcFinal := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, bytecodePoint, point, forms3, [total0, total1, total2]⟩

/-- `verifyBusBalance` as the depth's check, `busChallenges`, `gkrPhase` and `busRest`. -/
theorem verifyBusBalance_split (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout) :
    verifyBusBalance ev layout =
      (VerifierProgram.require (busDepth layout < 64)).bind fun _ ↦
      (busChallenges (busDepth layout)).bind fun wb ↦
      (gkrPhase (busDepth layout)).bind fun r ↦
        busRest ev layout wb.1 wb.2 r.2.1 r.2.2 := by
  simp only [verifyBusBalance, busChallenges, gkrPhase, busRest, VerifierProgram.bind_eq,
    VerifierProgram.pure_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

end
end LeanVM.Protocol.Verifier
