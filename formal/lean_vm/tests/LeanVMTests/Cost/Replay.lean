import LeanVM.Cost.Extractor.Replay
import LeanVM.Cost.Bounds.Replay
import LeanVMTests.Protocol.Verifier.Compiled

/-!
# Tests: the replay up to the stack's root, compiled

The compiled `afterRootLite` on the compiled verifier test's synthetic stream (`stream rate n`:
the eight announced sizes, memory `2^16`, rows `4, 2, 2, 4, 4, 8`, the rate exponent, two root
halves, then `n` scalars) and bytecode of 32 words: the program computes the function's value,
on an accepted shape (rate `4`), a rejected rate (`5`), a bad root half, and an empty stream.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Extraction.Fast LeanVM.Protocol.Compile
open LeanVMTests.Protocol.Verifier.Compiled

/-- The compiled `afterRootLite`'s value on the bytecode and a stream. -/
def afterRootRun (s : List LeanVM.Parameters.E) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList afterRootLiteC.costDeps) 1000 afterRootLiteC.costIdx
    [MachineEncoding.encodeValue sampleBytecode, MachineEncoding.encodeValue (⟨s, []⟩ : Proof)]

#guard (afterRootRun (stream 4 0)).map (·.1) ==
  some (MachineEncoding.encodeValue (afterRootLite sampleBytecode ⟨stream 4 0, []⟩))
#guard (afterRootLite sampleBytecode ⟨stream 4 0, []⟩).isSome
#guard ((afterRootLite sampleBytecode ⟨stream 4 0, []⟩).map fun r ↦ r.1.1.stackLog) == some 19
#guard (afterRootRun (stream 4 3)).map (·.1) ==
  some (MachineEncoding.encodeValue (afterRootLite sampleBytecode ⟨stream 4 3, []⟩))
#guard (afterRootRun (stream 5 0)).map (·.1) ==
  some (MachineEncoding.encodeValue (afterRootLite sampleBytecode ⟨stream 5 0, []⟩))
#guard (afterRootLite sampleBytecode ⟨stream 5 0, []⟩).isNone
#guard (afterRootRun (stream 4 0 1)).map (·.1) ==
  some (MachineEncoding.encodeValue (afterRootLite sampleBytecode ⟨stream 4 0 1, []⟩))
#guard (afterRootRun []).map (·.1) == some (MachineEncoding.encodeValue (afterRootLite sampleBytecode ⟨[], []⟩))

/-- info: some 3723256 -/
#guard_msgs in
#eval (afterRootRun (stream 4 0)).map (·.2)

/-- info: 'LeanVM.Cost.Bounds.afterRootLite_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.Bounds.afterRootLite_cost

end LeanVMTests.Cost
