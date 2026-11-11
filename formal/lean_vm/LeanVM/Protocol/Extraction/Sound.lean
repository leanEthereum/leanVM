/-
  LeanVM.Protocol.Extraction.Sound

  When the proof's extractor succeeds on an accepted proof, the knowledge extractor, reading the
  Keccak-256 answers of a prefix of the log, returns a valid execution.
-/

module

public import LeanVM.Protocol.Extraction.Halting
public import LeanVM.Protocol.Extraction.Extract

/-!
# The knowledge extractor succeeds where the proof's does

`extractor_of_extracted` is the one place the knowledge-soundness proof
(`knowledgeSoundness_holds`, `LeanVM/Protocol/LeanVMSound.lean`) meets the knowledge extractor
(`LeanVM/Protocol/Extraction/Extractor.lean`). Its hypotheses are the ones it had when the extractor was a classical choice; the proof now runs the algorithm:

* the verifier's steps 1 and 2 announce the layout, the rate and a root whose committed word is
  the extracted history's first word (`commitment_eq`), the word the prefix's answers commit to
  (`committedWord_eq`);
* the proof's candidate, a stack satisfying the leanISA relation, is a candidate of that word at
  the statement's Johnson threshold (`mem_candidates`, `OpeningIface.thr₀_eq`), and its
  execution, the capped halting run of its memory image, is valid
  (`Halting.candidateExecution_of_extracted`);
* the log has no collision, so its answers are injective (`answersInj_lookH`), and its support is
  finite, so the classically enumerated keys cover it (`keysCover_lookH`,
  `ExtractProofs.keysCover_supportKeys`);
* so the extractor, which decodes every candidate (`ExtractProofs.extract_of_candidate`), returns
  a valid execution.
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

/-- **When the proof's extractor succeeds on an accepted proof, the specification's, reading
the Keccak-256 answers of the first `k` entries of the log, returns a valid execution**, without
failure and when no hash entry past the first `k` answers the announced root: the proof's
candidate is a candidate of the word the root commits to, whose word is the history's
(`committedWord_eq`), and its memory image runs to a valid execution
(`Halting.candidateExecution_of_extracted`); the extractor decodes every candidate
(`ExtractProofs.extract_of_candidate`). -/
theorem extractor_of_extracted (O : OpeningIface) {X : Type} (σ : Seeds X) {ℓ : Log} {k : ℕ}
    {π : Proof}
    (hf : ¬ Fail σ ℓ)
    (hv : Rom.verify (lookH ℓ) (lookF ℓ) (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π = some true)
    (hroot : ∀ r, announcedRoot prog π = some r → ∀ x, .inl (x, r) ∉ ℓ.drop k)
    (hx : Extracted O prog input (cacheOf ℓ) π) :
    ∃ t, LeanVM.extractor prog input (cacheOf (ℓ.take k)) π = some t ∧
      ValidExecution prog input t := by
  obtain ⟨s₀, q₀, hx, hs₀, hM₀⟩ := hx
  unfold extractStack at hx
  dsimp only at hx
  split at hx
  · rename_i s ρ W hann hfw
    split at hx
    · rename_i hq
      obtain ⟨⟨root, ht, w, hroot', hW, st, haf, hhead⟩, hgood⟩ := commitment_eq hv hann hfw
      obtain ⟨q, hqc, hM⟩ := hq
      obtain ⟨t, hct, -⟩ := Halting.candidateExecution_of_extracted hgood.2.1 hM
      have hadm := hgood.2.2
      simp only [stackLog_verifierLayout] at hadm
      have hcand := mem_candidates (A' := Extraction.johnsonThreshold (leanIsaμ prog s) ρ) hqc
        (O.thr₀_eq hadm).ge
      have hWk : W = Extraction.committedWord (lookH (ℓ.take k)) root ht w :=
        hW.trans (committedWord_eq hf (hroot root hroot') ht w).symm
      rw [hWk] at hcand
      have hμ : 15 ≤ leanIsaμ prog s ∧ leanIsaμ prog s ≤ 28 := by
        have h1 := hadm.1
        have h2 := hadm.2.1
        unfold Whir.minLogStack at h1
        unfold Whir.maxLogStack at h2
        omega
      have hR : 1 ≤ ρ ∧ ρ ≤ 4 := by
        have h1 := hadm.2.2.1
        have h2 := hadm.2.2.2
        omega
      have hinj : Extraction.MerkleProofs.AnswersInj (lookH (ℓ.take k)) :=
        answersInj_lookH (not_fail_take hf k)
      have hcover : Extraction.MerkleProofs.KeysCover (lookH (ℓ.take k))
          (Extraction.supportKeys (lookH (ℓ.take k))) :=
        Extraction.ExtractProofs.keysCover_supportKeys
          (Extraction.ExtractProofs.finite_of_keysCover (keysCover_lookH (ℓ.take k)))
      exact Extraction.ExtractProofs.extract_of_candidate haf hhead hinj hcover
        (stackLog_verifierLayout prog s) hμ hR hcand hct
    · simp at hx
  · simp at hx

end
end LeanVM.Protocol.EndToEnd.Sound
