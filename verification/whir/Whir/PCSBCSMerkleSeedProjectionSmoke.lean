import Whir.PCSBCSMerkleSeedProjection

/-! Small real-BLAKE2s plans, source primitiveCalls, physical allocation traces,
and repeated observations. Counter-only negative cases avoid gigantic inputs. -/
set_option autoImplicit false
namespace Whir.PCSBCSMerkleSeedProjectionSmoke
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler
open PublicCompressionCouplingMixed

private def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"Merkle seed projection: {label}")
  IO.println s!"Merkle seed projection PASS: {label}"

private def raw : RawKey 16 → Digest32 := fun _ _ => 255
private def table : Key 16 → Digest32 := oracle blake2sOracle raw
private def bytes (size : Nat) : List Byte :=
  (List.range size).map fun n => ⟨n%256,Nat.mod_lt _ (by decide)⟩

private def runPlan (log : DuplexPublicSimulator.PublicLog) :
    List (Node × Digest32) → Bool × DuplexPublicSimulator.PublicLog × Nat
  | [] => (true,log,0)
  | (input,expected) :: rest =>
    let result := Sampling.execute table (primitiveCalls 16 log input)
    let later := runPlan result.1.1 rest
    (decide (result.1.2 = expected) && later.1,later.2.1,result.2.length+later.2.2)

private def twice (input : Node) : Program (Digest32 × Digest32) :=
  .ask (.primitive .direct input) fun first =>
    .ask (.primitive .verification input) fun second => .done (first,second)

private theorem twice_counted (input : Node) : Counts 2 (twice input) := by
  simp [twice,Counts,Query.cost]

private def smoke : IO Unit := do
  for size in [0,1,24,48,64,65,128,129] do
    let plan := PublicMerkleLog.plan blake2sOracle (bytes size)
    require s!"plan {size}: all nodes tag zero"
      (plan.all fun entry => decide (tag entry.1 = 0))
    require s!"plan {size}: no private-key rerouting"
      (plan.all fun entry => (DuplexPublicSimulator.privateKey 16 [] entry.1).isNone)
    let fresh := runPlan [] plan
    require s!"plan {size}: fresh source replies equal real BLAKE compression" fresh.1
    require s!"plan {size}: every fresh node allocates one draw"
      (fresh.2.2 == plan.length)
    let cached := runPlan fresh.2.1 plan
    require s!"plan {size}: cached replies remain authentic" cached.1
    require s!"plan {size}: cached nodes allocate no draw" (cached.2.2 == 0)
  let input := PublicMerkleLog.node DuplexCompression.parameterIV 0 (bytes 24) true
  let expected := blake2sOracle input
  let fresh := Sampling.execute table (primitiveCalls 16 [] input)
  require "fresh primitiveCalls draws exactly .inl input"
    (match fresh.2 with
      | [⟨.inl n,d⟩] => decide (n = input ∧ d = expected)
      | _ => false)
  let cached := Sampling.execute table (primitiveCalls 16 fresh.1.1 input)
  require "cached primitiveCalls retains public answer and has no physical draw"
    (decide (cached.1.2 = expected) && cached.2.isEmpty)
  let prior : Digest32 := fun _ => 17
  let inconsistent := Sampling.execute table (primitiveCalls 16 [(input,prior)] input)
  require "arbitrary cached public answer is retained, not silently seed-replaced"
    (decide (inconsistent.1.2 = prior) && inconsistent.2.isEmpty)
  let compiled := compile 16 DuplexCompression.parameterIV [] (twice input) 2
    (by decide) (twice_counted input)
  let execution := Sampling.execute table compiled
  require "actual mixed compile: two observations but only one physical seed draw"
    (execution.1.observations.length == 2 && execution.2.length == 1)
  require "actual mixed compile: both source replies equal the seed compression"
    (decide (execution.1.result = (expected,expected)))
  let oversized := PublicMerkleLog.node DuplexCompression.parameterIV (2^56) [] true
  require "unbounded ordinary-node tag-zero assumption is rejected at 2^56"
    (decide (tag oversized = 1 ∧ tag oversized ≠ 0))
  let terminal := PublicMerkleLog.node DuplexCompression.parameterIV (6*2^56) [] true
  require "unbounded ordinary-node nonterminal assumption is rejected"
    (decide (tag terminal = 6 ∧ isTerminal terminal))
  let wrapped := PublicMerkleLog.node DuplexCompression.parameterIV (2^64+1) [] true
  require "UInt64 wrap is not a substitute for the 56-bit source bound"
    (decide (wrapped.tweak.toNat = 1 ∧ tag wrapped = 0))

end Whir.PCSBCSMerkleSeedProjectionSmoke

def main : IO Unit := Whir.PCSBCSMerkleSeedProjectionSmoke.smoke
