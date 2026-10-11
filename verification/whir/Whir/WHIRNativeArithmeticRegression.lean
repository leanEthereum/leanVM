import Whir.WHIRNativeArithmetic
import Whir.WHIRNativeErasure

namespace Whir.WHIRNativeArithmeticRegression
open Concrete Protocol
open WHIRNativeArithmetic

private def e (n : Nat) : E := E.ofK (UInt64.ofNat n)
private def config : Config := ⟨3, #[1, 1], #[1, 1], #[2, 2], #[0, 1]⟩
private def challenges (a b : E) : Challenges :=
  ⟨#[⟨#[e 2], #[#[e 13, e 17]], #[e 43], a⟩,
     ⟨#[e 3], #[], #[e 47], b⟩], #[e 5]⟩
private def witness : Array K := #[1, 7, 19, 5, 42, 99, 31, 11]
private def callerPoint : Array E := #[e 23, e 29, e 31]
private def callerWeight : Array E := eqTable callerPoint
private def callerAt (point : Array E) : E :=
  AccumulatedTerminalAlgebra.equalityProduct callerPoint.toList point.toList

private def expectOk (label : String) (result : Except String Unit) : IO Unit :=
  match result with
  | .ok () => pure ()
  | .error message => throw (IO.userError s!"{label}: {message}")

private def expectError (label expected : String) (result : Except String Unit) : IO Unit :=
  match result with
  | .error message =>
    unless message == expected do throw (IO.userError s!"{label}: wrong error {message}")
  | .ok () => throw (IO.userError s!"{label}: unexpectedly accepted")

private def runCase (label : String) (a b : E) (negative : Bool) : IO Unit := do
  let ch := challenges a b
  let target := dot (witness.map E.ofK) callerWeight
  let (root, proof) ← match Protocol.prove config ch witness callerWeight target with
    | .ok result => pure result
    | .error message => throw (IO.userError s!"prover: {message}")
  expectOk (label ++ "/dense") (Protocol.verify config ch 2 root callerWeight target proof)
  let physical := WHIRPhysicalErasure.eraseOracles proof
  expectOk (label ++ "/native") (nativeVerify config ch 2 target callerAt physical)
  if negative then
    expectError "wrong target" "terminal mismatch" (nativeVerify config ch 2 (target+1) callerAt physical)
    let alteredIntro := { physical with initial := {physical.initial with u0 := physical.initial.u0+1} }
    expectError "altered initial scalar" "terminal mismatch" (nativeVerify config ch 2 target callerAt alteredIntro)
    let first := physical.levels[0]!
    let last := physical.levels[1]!
    let missing := { physical with levels := physical.levels.set! 0 {first with nextOracle := none} }
    expectError "missing commitment" "missing commitment" (nativeVerify config ch 2 target callerAt missing)
    let extra := { physical with levels := physical.levels.set! 1 {last with nextOracle := some #[]} }
    expectError "extra final commitment" "final length" (nativeVerify config ch 2 target callerAt extra)
    let wrongResidual := { physical with residual := physical.residual.pop }
    expectError "wrong residual length" "final length" (nativeVerify config ch 2 target callerAt wrongResidual)
    let wrongRows := { physical with levels := physical.levels.set! 0 {first with rows := first.rows.pop} }
    expectError "wrong query row count" "query length" (nativeVerify config ch 2 target callerAt wrongRows)
    let wrongFolds := { physical with levels := physical.levels.set! 0 {first with afterFold := first.afterFold.pop} }
    expectError "wrong fold scalar count" "round/OOD length" (nativeVerify config ch 2 target callerAt wrongFolds)
    let wrongOod := { physical with levels := physical.levels.set! 0 {first with oods := #[]} }
    expectError "wrong OOD scalar count" "round/OOD length" (nativeVerify config ch 2 target callerAt wrongOod)
    let wrongTail := { physical with tailMessages := #[⟨0, 0⟩] }
    expectError "wrong tail scalar count" "proof length" (nativeVerify config ch 2 target callerAt wrongTail)
    expectError "zero lanes" "configuration/challenges/weight" (nativeVerify config ch 0 target callerAt physical)
    expectError "too many lanes" "configuration/challenges/weight" (nativeVerify config ch 3 target callerAt physical)
    let malformed := { ch with levels := ch.levels.set! 0 { ch.levels[0]! with oodPoints := #[#[e 13]] } }
    expectError "wrong OOD dimension" "configuration/challenges/weight"
      (nativeVerify config malformed 2 target callerAt physical)
  IO.println s!"{label}: dense and scalar-only erased-root verifier accept"

#eval do
  runCase "two-level source arithmetic/nonzero glue" (e 7) (e 11) true
  runCase "zero first glue" 0 (e 11) false
  runCase "zero second glue" (e 7) 0 false
  runCase "zero all glue" 0 0 false
  IO.println "scalar tampering and all exercised length/presence/dimension guards reject"

private def family : Fin 2 → RingPCSGame.FamilyClaim := fun j =>
  if j.val = 0 then ⟨0, #[e 13, e 17], fun _ => 0⟩
  else ⟨4, #[e 19, e 23], fun _ => 0⟩
private def points : Array RingPCSGame.PointClaim :=
  #[.point 0 #[e 29, e 31] 0, .strided 4 1 1 #[e 37] 0]
private def seed : RingPCSGame.Prefix := (⟨3, 1, 0⟩, fun i => e (i.val + 2))

#eval do
  let ch := challenges (e 7) (e 11)
  let weight := (CausalGame.batchClaims 8 (RingPCSGame.transformedClaims 8 family points seed) (e 41)).weight
  let target := dot (witness.map E.ofK) weight
  let (root, proof) ← match Protocol.prove config ch witness weight target with
    | .ok result => pure result
    | .error message => throw (IO.userError s!"full caller prover: {message}")
  expectOk "full caller dense" (Protocol.verify config ch 2 root weight target proof)
  expectOk "full caller source" (sourceNativeVerify family points seed (e 41) config ch 2 target
    (WHIRPhysicalErasure.eraseOracles proof))
  IO.println "full source ring family + ordinary/strided points: scalar-only verifier accepts"
  let honestPoints := points.set! 0 (.point 0 #[e 29, e 31] (target.scale (kinv 41)))
  let scalarTarget := WHIRNativeArithmetic.initialClaim family honestPoints seed (e 41)
  unless scalarTarget == target do
    throw (IO.userError "scalar initial claim disagrees with honest witness target")
  let projected := (CausalGame.batchClaims 0
    (RingPCSGame.transformedClaims 0 family honestPoints seed) (e 41)).value
  unless scalarTarget == projected do
    throw (IO.userError "scalar initial claim disagrees with width-independent dense projection")
  expectOk "full source initial/final arithmetic"
    (sourceVerify family honestPoints seed (e 41) config ch 2 (WHIRPhysicalErasure.eraseOracles proof))
  IO.println "source-computed initial claim and final weight: full verifier accepts"

#print axioms WHIRNativeArithmetic.nativeVerify_refines
#print axioms WHIRNativeArithmetic.sourceNativeVerify_refines
#print axioms WHIRNativeArithmetic.verifyLevel_refines
#print axioms WHIRNativeErasure.nativeVerify_erased
#print axioms WHIRNativeArithmetic.initialClaim_eq_batch_value
#print axioms WHIRNativeArithmetic.sourceVerify_refines

end Whir.WHIRNativeArithmeticRegression
