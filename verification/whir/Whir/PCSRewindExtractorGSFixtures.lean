import Whir.InterleavedListExtraction

/-! Independent non-unique-radius extension-field GS regression artifact.
This backend is not imported or executed by the Root0 knowledge extractor. -/
namespace Whir.PCSRewindExtractorGSFixtures
open Concrete

def extensionRows : Fin 2 → Array E := fun lane =>
  Array.ofFn fun j : Fin 4 => ⟨UInt64.ofNat (3 + lane.val * 11 + j.val),
    UInt64.ofNat (5 + j.val), UInt64.ofNat (7 + lane.val)⟩

def runGS : IO Unit := do
  let encoded := Array.ofFn fun lane : Fin 2 => encode 2 2 (extensionRows lane)
  let received : Fin 2 → Fin 16 → E := fun lane q =>
    if q.val < 8 then (encoded[lane.val]!)[q.val]!
    else (encoded[lane.val]!)[q.val]! + E.ofK 1
  let decoded := InterleavedListExtraction.candidates 2 2 2 8 2 15 false received
  let expected := InterleavedListExtraction.assemble 2 false (List.ofFn extensionRows)
  unless decoded.contains expected do throw (IO.userError "non-unique-radius interleaved GS target missing")
  IO.println s!"interleaved-GS: 2 genuine E lanes, k=4, N=16, errors=8, candidates={decoded.length}"

end Whir.PCSRewindExtractorGSFixtures

def main : IO Unit := Whir.PCSRewindExtractorGSFixtures.runGS
