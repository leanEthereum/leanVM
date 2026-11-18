module

public import LeanVM.Cost.AS.Within
public import LeanVM.Cost.AS.ProgramSize
public import LeanVM.Cost.AS.Glue
import all LeanVM.Protocol.Extraction.AS.Lite

/-!
# The extractor the compiled agreement-set program computes

**`asExtractor_output`**: `compiledASExtractor` (its entry at `0`, its bodies held,
`asProgram_includes_all`), run within a size bound `S` at least its size and within `asBudget` at
the stack size the proof announces and the transcript's number of permutation queries (or any larger
budget), outputs,
decoded, what `transcriptExtractorL` returns: where the extraction succeeds its price is within the
budget (`extractL_cost`, `asPrice_le`, `announced_of_decSizesL`).
-/

namespace LeanVM.Cost.AS

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Extraction.AS
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Cost.Bounds.AS Common

public section

/-- The program holds its bodies: their indices are distinct (`asProgram_indices_increasing`). -/
theorem asProgram_includes_all : Includes compiledASExtractor asProgramBodies := by
  have h := nodup_of_increasing asProgram_indices_increasing
  refine includes_ofList _ ?_
  rw [asProgramBodies, List.map_cons]
  exact h

theorem asProgram_includes : Includes compiledASExtractor extractLC.costDeps :=
  asProgram_includes_all.mono fun _ hp ↦ by rw [asProgramBodies]; exact List.mem_cons_of_mem _ hp

theorem asProgram_entry : compiledASExtractor[0]? = some (entryBody extractLC.costIdx) :=
  asProgram_includes_all.get (by rw [asProgramBodies]; exact List.mem_cons_self)

/-- **The compiled agreement-set extractor's price within `asBudget`** where it succeeds, the
entry's `14` included, at the stack size the proof announces. -/
theorem asPrice_within (prog : LeanIsaProgram) (input : PublicInput) (T : OracleQueryLog) (π : Proof)
    (t : Execution prog) (ht : extractL prog input (permutationQueries T) π = some t) :
    machineCost compiledASExtractor extractLC.costIdx [encodeValue prog, encodeValue input,
        encodeValue (permutationQueries T), encodeValue π] + 14 ≤
      asBudget (announcedStackLog prog π) (permutationQueries T).length := by
  obtain ⟨seed, r₁, lay, ρ, r₂, tr, h2, h3, h4, h5, hc⟩ :=
    extractL_cost compiledASExtractor asProgram_includes prog input (permutationQueries T) π ht
  rw [announced_of_decSizesL _ prog π seed h2 h3]
  obtain ⟨hF, hρ1, hρ2, hs1, hs2⟩ := decSizesL_facts h3
  obtain ⟨-, -, hsh⟩ := extract_trace h3 h5
  have hb := asPrice_le (permutationQueries T).length prog.logSize lay ρ tr r₂.2.roots prog.logSize_le hF
    hs1 hs2 hρ1 hρ2 (extract_roots h2 h3 h4) hsh
  omega

/-- **The extractor `compiledASExtractor` computes**, within a size bound at least its size and
within any budget `B` at least `asBudget`, is `transcriptExtractorL`. -/
theorem asExtractor_output (S : ℕ) (hS : compiledASExtractor.size ≤ S) (B : ℕ → ℕ → ℕ)
    (hB : ∀ μ N, asBudget μ N ≤ B μ N) (prog : LeanIsaProgram)
    (input : PublicInput) (T : OracleQueryLog) (proof : Proof) :
    (outputWithin compiledASExtractor S
        (B (announcedStackLog prog proof) (permutationQueries T).length)
        (encodeLeanVmKnowledgeExtractorInput prog input T proof)).bind (decodeExecution prog) =
      transcriptExtractorL prog input T proof :=
  asOutput compiledASExtractor S hS extractLC.costIdx asProgram_entry
    (fun prog input qs π ↦ machineCost compiledASExtractor extractLC.costIdx
      [encodeValue prog, encodeValue input, encodeValue qs, encodeValue π])
    (fun prog input qs π ↦ extractLC.costSpec compiledASExtractor asProgram_includes prog input qs π)
    prog input T proof _ fun t ht ↦ (asPrice_within prog input T proof t ht).trans (hB _ _)
end

end LeanVM.Cost.AS
