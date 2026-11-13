import LeanVM.Cost.Extractor.Top
import LeanVMTests.Runs

/-!
# Tests: the compiled list decoder, end to end

The extractor's compiled list decoder (`decOfC`, `decOf` = `decodeStacksDistinctPM` on the
committed leaves, `Cost/Extractor/Top.lean`), run on the cost machine, against the proof side's
reference decoder (`decodeStacksDistinct`, Lee–O'Sullivan and Mulders–Storjohann, evaluated
directly) on a toy word: `μ = 9`, `R = 1` (`2^9` stack entries, `64` lanes of `16` columns,
messages of `2^3 + 6 = 14` coefficients, agreement `15`, multiplicity `1`), each lane a polynomial
of degree `< 14` with at most one corrupted symbol (the same column), so every lane decodes and
the pruning runs over all `64` lanes. The admissible shapes (`μ ≥ 15`) are out of reach of a
test: at `(15, 1)` a lane already interpolates at multiplicity `7` on `1024` points. The run is
compiled (`runs`, run by `lake exe test-runs`): interpreted, it is the slowest test.
-/

namespace LeanVMTests.Cost.DecOf

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast

def rnd (s : ℕ) : K := K.ofBits ((s * 2654435761 + 12345) % 4294967291)

/-- Lane `u`'s symbol at column `v`: a polynomial of degree `< 14` at `x_v`, corrupted at column
`1` on every third lane (the survivors agree with the word on the columns all lanes agree on,
`15 ≥ A`). -/
def sym (u v : ℕ) : K :=
  if u % 3 == 0 && v == 1 then rnd (7000 + u)
  else (List.range 14).foldr (fun j acc ↦ rnd (100 * u + j) + K.ofBits v * acc) 0

/-- The `16` committed leaves, `64` symbols each (lane `u` at position `63 − u`, `laneSymbol`). -/
def leaves : Array (List K) :=
  Array.ofFn fun v : Fin 16 ↦ (List.ofFn fun u : Fin 64 ↦ sym u v.val).reverse

/-- The reference decoding is one stack, the survivor of every lane, and the compiled decoder's
value. -/
test_runs runs := [
  ("decOfC is the reference decoder on a toy word", fun _ ↦
    let r := decodeStacksDistinct 9 1 (leafAt leaves 4 64)
    r.length == 1 &&
      (evaluateFunctionBody (MachineProgram.ofList decOfC.costDeps) 1000000000 decOfC.costIdx
        [MachineEncoding.encodeValue (9 : ℕ), MachineEncoding.encodeValue (1 : ℕ),
          MachineEncoding.encodeValue leaves, MachineEncoding.encodeValue (4 : ℕ),
          MachineEncoding.encodeValue (64 : ℕ)]).map (·.1) ==
        some (MachineEncoding.encodeValue r))]

end LeanVMTests.Cost.DecOf
