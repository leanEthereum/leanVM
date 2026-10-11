import Whir.AnchoredByteStreamSampler

/-! Executable byte-codec fixture, not a replacement oracle or a cryptographic
assumption. Coordinate one consumes the fourth word of block zero and then the
first two words of block one. All public answers are recovered exactly. -/
namespace Whir.AnchoredByteStreamSmoke
open Concrete FiatShamirGame AnchoredFiatShamirSecurityCodec

def fixture : Blocks 3 := fun block byte =>
  ⟨32*block.val+byte.val, by have hb : block.val < 3 := block.isLt; have := byte.isLt; omega⟩

def decodedBytes : List (List Nat) := List.ofFn (fun j : Fin 3 =>
  List.ofFn (fun i : Fin 24 => (ByteCodec.encodeE (point 3 fixture j) i).val))

def expected : List (List Nat) := List.ofFn (fun j : Fin 3 =>
  List.ofFn (fun i : Fin 24 => 24*j.val+i.val))

def straddlingSmoke : Bool := decodedBytes == expected &&
  decide (blockCount 28 = 21) && decide (residualCount 3 = 24) &&
  decide ((vectorParts 3 fixture).2 ⟨0,by decide⟩ = (⟨72,by decide⟩ : Byte))

#eval straddlingSmoke

example : blockCount 28 = 21 := by decide +kernel
example : residualCount 3 = 24 := by decide +kernel

/-- The first byte of the second scalar really is the observable fourth word,
not the first word of a second independent digest. -/
example : (ByteCodec.encodeE (point 3 fixture ⟨1,by decide⟩) ⟨0,by decide⟩).val = 24 := by
  decide +kernel

example : (ByteCodec.encodeE (point 3 fixture ⟨1,by decide⟩) ⟨8,by decide⟩).val = 32 := by
  decide +kernel

end Whir.AnchoredByteStreamSmoke

def main : IO Unit := do
  unless Whir.AnchoredByteStreamSmoke.straddlingSmoke do
    throw (IO.userError "Byte-stream scalar straddling or retained-suffix check failed")
  IO.println "byte_stream_smoke=passed: contiguous scalars, fourth-word straddling, retained suffix"
