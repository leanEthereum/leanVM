import LeanVM.Cost.Extractor.Transcript
import LeanVM.Cost.Extractor.Top

/-!
# Tests: the compiled transcript index, leaf reader and fast path run

The program of each compiled function's bodies computes the function's value.
-/

namespace LeanVMTests.Cost.Extractor

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics Common

attribute [local instance] lexOrd

/-- Two forward queries from the zero state. -/
def qs : List (PermutationQuery KeccakState × KeccakState) :=
  [(.forward (Vector.replicate 25 0), Vector.ofFn fun i ↦ (i.val + 1).toUInt64),
   (.forward (Vector.ofFn fun i ↦ if i.val < 17 then 7 else 0), Vector.replicate 25 3)]

#guard (evaluateFunctionBody (MachineProgram.ofList transcriptIndexC.costDeps) 100000
    transcriptIndexC.costIdx [MachineEncoding.encodeValue qs, MachineEncoding.encodeValue (64 : ℕ)]).map (·.1) ==
  some (MachineEncoding.encodeValue (transcriptIndex qs 64))

def leaves : Array (List K) := #[[K.ofBits 1, K.ofBits 2], [K.ofBits 3, K.ofBits 4]]

#guard (evaluateFunctionBody (MachineProgram.ofList leafAtC.costDeps) 1000 leafAtC.costIdx
    [MachineEncoding.encodeValue leaves, MachineEncoding.encodeValue (1 : ℕ), MachineEncoding.encodeValue (2 : ℕ), MachineEncoding.encodeValue (3 : ℕ)]).map (·.1) ==
  some (MachineEncoding.encodeValue (leafAt leaves 1 2 3))

/-- A committed word of `2^7` columns (`κ = 1`, `R = 0`, height 7, width 64): the fast path. -/
def leaves7 : Array (List K) :=
  Array.ofFn fun v : Fin 128 ↦ (List.range 2).map fun u ↦ K.ofBits (u + v.val)

#guard (evaluateFunctionBody (MachineProgram.ofList fastOfC.costDeps) 100000000 fastOfC.costIdx
    [MachineEncoding.encodeValue (7 : ℕ), MachineEncoding.encodeValue (0 : ℕ), MachineEncoding.encodeValue leaves7, MachineEncoding.encodeValue (7 : ℕ), MachineEncoding.encodeValue (64 : ℕ)]).map
    (·.1) == some (MachineEncoding.encodeValue (fastOf 7 0 leaves7 7 64))

end LeanVMTests.Cost.Extractor
