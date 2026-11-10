import LeanVM.Cost.Extractor.Top
import LeanVMTests.Protocol.Verifier.Compiled

/-!
# Tests: the compiled extractor

The compiled `extractorTop` on a two-instruction program and proofs the replay rejects (an empty
stream, a rejected rate): the program computes the extractor's value (`none`), and the program's
size and index. The spec's and the price equation's axioms are Lean's three.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Extraction.Fast LeanVM.Protocol.Compile
open LeanVMTests.Protocol.Verifier.Compiled LeanVM.Semantics LeanVM.Parameters

/-- A program of two `JUMP`s. -/
def tinyProg : LeanVM.Semantics.LeanIsaProgram := ⟨1, by decide, fun _ ↦ .jump 0 0 0⟩

def tinyInput : PublicInput := ⟨fun _ ↦ 0⟩

/-- The compiled extractor's value on a stream. -/
def extractorRun (s : List E) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList extractorC.costDeps) 10000 extractorC.costIdx
    [MachineEncoding.encodeValue tinyProg, MachineEncoding.encodeValue tinyInput,
      MachineEncoding.encodeValue ([] : List (Common.PermutationQuery KeccakState × KeccakState)),
      MachineEncoding.encodeValue (⟨s, []⟩ : Proof)]

#guard (extractorRun []).map (·.1) ==
  some (MachineEncoding.encodeValue (extractorTop tinyProg tinyInput [] ⟨[], []⟩))
#guard (extractorTop tinyProg tinyInput [] ⟨[], []⟩).isNone
#guard (extractorRun (stream 5 0)).map (·.1) ==
  some (MachineEncoding.encodeValue (extractorTop tinyProg tinyInput [] ⟨stream 5 0, []⟩))

/-- info: 699 -/
#guard_msgs in
#eval extractorC.costDeps.length

/-- info: 'LeanVM.Cost.Extractor.extractorC.costSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms extractorC.costSpec

/-- info: 'LeanVM.Cost.Extractor.extractorC.costEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms extractorC.costEq

end LeanVMTests.Cost
