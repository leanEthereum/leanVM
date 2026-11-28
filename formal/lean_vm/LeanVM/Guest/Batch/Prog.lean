/-
  LeanVM.Guest.Batch.Prog

  The batching as a program of the verifier language: the count, the children's claims and the
  sumcheck's messages are prover scalars, the lambdas and the sumcheck's challenges are samples.
-/

module

public import Statement.LeanVmGuestCompleteness
import LeanVM.Protocol.KeccakHash
import LeanVM.Parameters.Generator
import LeanVM.Parameters.Field

/-!
# The batching's cells

The batching program (`boundedBatchingProgram M bytecode`, `Statement/LeanVmGuestCompleteness.lean`)
reads the count `g^n` and three zeros, then each child's words and the zeros to a whole rate
(`childCells`): its public input's two halves, its fresh claim's point and values, its carried
claim's point and value. For a child of the split program's shapes (`ChildHasBytecodeShape`), the
cells are `childWordCount` words then the padding (`childCells_eq`), and the child is read back off
them (`parseChild_childCells`); below `M ≤ 2^64 - 1` the count is read back off its power
(`countOf_gpow`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The cells -/

theorem padRate_eq (ws : List E) : padToRate ws = ws ++ List.replicate (zerosToWholeRate ws.length) 0 := rfl

theorem length_words {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    c.words.length = childWordCount bytecode := by
  obtain ⟨h1, h2, h3⟩ := hc
  simp only [DeferredBytecodeClaim.HasBytecodeShape] at h3
  simp [ChildClaims.words, FreshClaim.cells, DeferredBytecodeClaim.cells, childWordCount, h1, h2,
    h3]
  omega

/-- A child of the split program's shapes has `childWordCount` words, then the padding. -/
theorem childCells_eq {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    childCells c = c.words ++
      List.replicate (zerosToWholeRate (childWordCount bytecode)) 0 := by
  rw [childCells, padRate_eq, length_words hc]

theorem length_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    (childCells c).length =
      childWordCount bytecode + zerosToWholeRate (childWordCount bytecode) := by
  rw [childCells_eq hc, List.length_append, length_words hc, List.length_replicate]

/-- A child of the split program's shapes is read back off its words, padded or not. -/
theorem parseChild_append {bytecode : List K} {c : ChildClaims}
    (hc : ChildHasBytecodeShape bytecode c) (pad : List E) :
    parseChild bytecode (c.words ++ pad) = c := by
  obtain ⟨pi, ⟨fp, fv⟩, ⟨bp, bv⟩⟩ := c
  obtain ⟨h1, h2, h3⟩ := hc
  simp only [DeferredBytecodeClaim.HasBytecodeShape] at h1 h2 h3
  simp [parseChild, ChildClaims.words, FreshClaim.cells, DeferredBytecodeClaim.cells,
    digestOfScalars_digestScalars, List.getD_eq_getElem?_getD, List.drop_append, h1, h2, h3,
    List.drop_eq_nil_of_le]

theorem parseChild_words {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    parseChild bytecode c.words = c := by
  simpa using parseChild_append hc []

/-- The padded words are read back off. -/
theorem parseChild_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    parseChild bytecode (childCells c) = c := by
  rw [childCells_eq hc]
  exact parseChild_append hc _

theorem drop_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    (childCells c).drop (childWordCount bytecode) =
      List.replicate (zerosToWholeRate (childWordCount bytecode)) 0 := by
  rw [childCells_eq hc, List.drop_left' (length_words hc)]

/-- The count's power is read back below `M ≤ 2^64 - 1`. -/
theorem countOf_gpow {M n : ℕ} (hM : M ≤ 2 ^ 64 - 1) (hn : n < M) :
    childCountOfGeneratorPower M (Verifier.gpow n) = some n := by
  have hex : ∃ m, m < M ∧ Verifier.gpow m = Verifier.gpow n := ⟨n, hn, rfl⟩
  rw [childCountOfGeneratorPower, dite_eq_left hex, Option.some.injEq]
  generalize hk : Nat.find hex = k at *
  obtain ⟨hlt, hs⟩ : k < M ∧ Verifier.gpow k = Verifier.gpow n := hk ▸ Nat.find_spec hex
  have hK : ∀ m, Verifier.gpow m = ofK (Parameters.addressOfIndex m) := fun m ↦ by
    show gen ^ m = algebraMap K E (g ^ m)
    rw [map_pow]
    rfl
  rw [hK k, hK n] at hs
  exact gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (ofK_injective hs)

theorem headCells_eq (n : ℕ) : childCountCells n = [Verifier.gpow n, 0, 0, 0] := rfl

end
end LeanVM.Guest.Batch
