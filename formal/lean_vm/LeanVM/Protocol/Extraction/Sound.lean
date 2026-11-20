/-
  LeanVM.Protocol.Extraction.Sound

  The hash inputs of a log cover its hash answers.
-/

module

public import LeanVM.Protocol.Extraction.Halting
public import LeanVM.Protocol.Extraction.Extract

/-!
# The hash inputs of a log

`keysCover_lookH`: the hash inputs of a log cover its hash answers, so the classically enumerated
keys of a log's answers (`ExtractProofs.keysCover_supportKeys`) are the extractor's keys.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open OracleComp OracleSpec

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

variable {prog : LeanIsaProgram} {input : PublicInput}

/-- **The hash inputs of a log cover its hash answers.** -/
theorem keysCover_lookH (ℓ : Log) : Extraction.MerkleProofs.KeysCover (lookH ℓ) (hIns ℓ) := by
  intro x d h
  obtain ⟨i, hi, hei, -⟩ := (lookH_eq_some_iff ℓ x d).mp h
  have hmem : (.inl (x, d) : Entry) ∈ ℓ := by
    rw [← hei]
    exact List.getElem_mem hi
  exact List.mem_map.mpr ⟨(x, d), mem_leftOf.mpr hmem, rfl⟩

end
end LeanVM.Protocol.EndToEnd.Sound
