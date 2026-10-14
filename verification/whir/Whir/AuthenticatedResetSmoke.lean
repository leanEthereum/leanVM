import Whir.AuthenticatedResetCollector

/-! Compiled, actual-verifier fixtures: a zero honest prover, a partially
accepting withholding prover, and malformed query tags. No probability space
or field-element enumeration is evaluated by these executable tests. -/
namespace Whir.AuthenticatedResetSmoke
open Concrete Protocol CausalGame KnowledgeExtraction AuthenticatedResetSupport

def config : Config := ⟨3, #[1, 1], #[1, 1], #[2, 2], #[0, 0]⟩
def input : Public := ⟨config, 1, tab 8 (fun _ => #[0]), #[]⟩
def message : Message E := ⟨0, 0⟩

def honest : Strategy := fun _ _ batch =>
  match batch with
  | .initial _ => .initial message
  | .fold level _ _ => .fold message
      (if level = 0 then some (tab 4 fun _ => #[0, 0]) else none)
      (if level = 1 then #[0, 0] else #[])
  | .ood _ _ _ => .ood ⟨0, message⟩
  | .query level _ _ => .query (tab 2 fun _ => if level = 0 then #[0] else #[0, 0]) message
  | .tail _ _ => .tail message

def withholding : Strategy := fun statement past batch =>
  match batch with
  | .query 0 squeezes _ =>
    if squeezes[0]!.c0 == 1 then .query #[] message else honest statement past batch
  | _ => honest statement past batch

def malformed : Strategy := fun statement past batch =>
  match batch with
  | .query _ _ _ => .tail message
  | _ => honest statement past batch

def tape (x : K) : Tape config :=
  (0, (fun i => (fun _ => 0, (fun _ _ => 0),
    (fun _ => if i.val = 0 then E.ofK x else 0), 0)), fun _ => 0)

def check : IO Unit := do
  let level : Fin config.folds.size := ⟨0, by decide⟩
  let tapes := [tape 0, tape 1]
  let honestProver : CommittedProver := ⟨input, honest⟩
  let withholdingProver : CommittedProver := ⟨input, withholding⟩
  let malformedProver : CommittedProver := ⟨input, malformed⟩
  let h := collectedRecords honestProver level 3 tapes
  let w := collectedRecords withholdingProver level 3 tapes
  let m := collectedRecords malformedProver level 3 tapes
  let result := runRewind input withholding 5 (collectionFuel input tapes)
    (collectAcceptedProgram input level 3 tapes (fun _ => none))
  if experiment input honest (tape 0) != true || experiment input honest (tape 1) != true then
    throw (IO.userError "honest verifier trial rejected")
  if experiment input withholding (tape 0) != true || experiment input withholding (tape 1) != false then
    throw (IO.userError "withholding acceptance gate failed")
  if experiment input malformed (tape 0) != false then
    throw (IO.userError "malformed tag accepted")
  if h.length != 4 || w.length != 2 || m.length != 0 || result.responseCalls != 30 then
    throw (IO.userError "collected data/replay count mismatch")
  IO.println s!"actual verifier: honest 2/2, withholding 1/2, malformed 0/2; records {h.length}/{w.length}/{m.length}; response/replay calls {result.responseCalls}"
end Whir.AuthenticatedResetSmoke

def main : IO Unit := Whir.AuthenticatedResetSmoke.check
