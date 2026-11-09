import LeanVM.Cost.Extractor.Top

/-!
# Tests: the compiled list decoder, end to end

The extractor's compiled list decoder (`decOfC`, `decOf` = `decodeStacksDistinctPM` on the
committed leaves, `Cost/Extractor/Top.lean`), run on the cost machine, against the proof side's
reference decoder (`decodeStacksDistinct`, Lee–O'Sullivan and Mulders–Storjohann, evaluated
directly) on a toy word: `μ = 7`, `R = 1` (`2^7` stack entries, `64` lanes of `4` columns,
agreement `3`, multiplicity `1`, list size `2`), each lane a line with at most one corrupted
symbol (the same column), so every lane decodes and the pruning runs over all `64` lanes. The admissible shapes
(`μ ≥ 15`) are out of reach of a test: at `(15, 1)` a lane already interpolates at multiplicity
`169` on `1024` points.
-/

namespace LeanVMTests.Cost.DecOf

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast

def rnd (s : ℕ) : K := K.ofBits ((s * 2654435761 + 12345) % 4294967291)

/-- Lane `u`'s symbol at column `v`: the line `a_u + b_u·x_v`, corrupted at column `1` on every
third lane (the survivors agree with the word on the columns all lanes agree on, `3 ≥ A`). -/
def sym (u v : ℕ) : K :=
  if u % 3 == 0 && v == 1 then rnd (7000 + u)
  else rnd (2 * u) + rnd (2 * u + 1) * K.ofBits v

/-- The `4` committed leaves, `64` symbols each (lane `u` at position `63 − u`, `laneSymbol`). -/
def leaves : Array (List K) := Array.ofFn fun v : Fin 4 ↦ (List.ofFn fun u : Fin 64 ↦ sym u v.val).reverse

/-- The reference decoding: one stack, the survivor of every lane. -/
def ref : List (Vector K (2 ^ 7)) := decodeStacksDistinct 7 1 (leafAt leaves 2 64)

#guard
  let r := ref
  r.length == 1 &&
    (evaluateFunctionBody (MachineProgram.ofList decOfC.costDeps) 1000000000 decOfC.costIdx
      [MachineEncoding.encodeValue (7 : ℕ), MachineEncoding.encodeValue (1 : ℕ),
        MachineEncoding.encodeValue leaves, MachineEncoding.encodeValue (2 : ℕ),
        MachineEncoding.encodeValue (64 : ℕ)]).map (·.1) ==
      some (MachineEncoding.encodeValue r)

end LeanVMTests.Cost.DecOf
