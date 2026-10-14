import Whir.PCSBCSPublicCallerAnswersCost

namespace Whir.PCSBCSPublicCallerAnswersSmoke
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicCompressionProgram PublicMerkleLog PCSBCSPublicCallerAnswers

private def bytes (n : Nat) : List Byte :=
  (List.range n).map fun i => ⟨(13*i+7)%256,Nat.mod_lt _ (by decide)⟩

private def digest (salt : Nat) : Digest32 := fun i =>
  ⟨(17*i.val+salt)%256,Nat.mod_lt _ (by decide)⟩

private def recordPlan (cv : Digest32) : List DuplexEncoding.Instruction → PublicLog
  | [] => []
  | instruction :: rest =>
      let node : Node := ⟨cv,instruction.1,instruction.2,true⟩
      let stored := Array.ofFn (blake2sOracle node)
      let result : Digest32 := fun i => stored[i.val]'(by simp [stored])
      (node,result) :: recordPlan result rest

private def check (label : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError (label ++ ": FAILED"))

private def runCase (size block : Nat) : IO Unit := do
  let coordinate : Coordinate :=
    ⟨⟨digest 1,digest 2,[.absorb 0 (bytes size)]⟩,.output block⟩
  let plan := DuplexEncoding.plan coordinate
  let log := recordPlan DuplexCompression.parameterIV plan
  let expected := log.getLast?.map Prod.snd
  check "actual recorded caller digest" (answer? log DuplexCompression.parameterIV coordinate == expected)
  check "reordered authentic cache" (answer? log.reverse DuplexCompression.parameterIV coordinate == expected)
  check "missing terminal physical input rejects" ((answer? log.dropLast DuplexCompression.parameterIV coordinate).isNone)
  check "missing seed input rejects" ((answer? log.tail DuplexCompression.parameterIV coordinate).isNone)
  let counted := replayFromCounted log DuplexCompression.parameterIV plan
  check "counted replay preserves real digest" (counted.1 == expected)
  check "reached lookup comparisons" (counted.2 == plan.length*(plan.length+1)/2+plan.length+1)
  let absent := replayFromCounted [] DuplexCompression.parameterIV plan
  check "missing earlier prefix has no synthetic answer" (absent.1.isNone && absent.2 == 1)
  check "wrong source domain rejects" ((answer? log DuplexCompression.parameterIV
    {coordinate with history := {coordinate.history with domain := digest 3}}).isNone)
  check "wrong output coordinate rejects" ((answer? log DuplexCompression.parameterIV
    {coordinate with terminal := .output (block+1)}).isNone)

private def smoke : IO Unit := do
  for size in [0,1,24,64,65,128,129] do
    runCase size 0
    runCase size 1
  let coordinate : Coordinate := ⟨⟨digest 1,digest 2,[]⟩,.output 0⟩
  let log := recordPlan DuplexCompression.parameterIV (DuplexEncoding.plan coordinate)
  let wrong := digest 99
  match log with
  | [] => throw (IO.userError "fixture produced no physical plan")
  | (node,_)::rest =>
      check "inconsistent earlier cache cannot authenticate a caller stream"
        ((answer? ((node,wrong)::rest) DuplexCompression.parameterIV coordinate).isNone)
  IO.println "Real BLAKE2s public caller replay: complete/reordered, missing/foreign, counted bounds OK"

end Whir.PCSBCSPublicCallerAnswersSmoke

def main : IO Unit := Whir.PCSBCSPublicCallerAnswersSmoke.smoke
