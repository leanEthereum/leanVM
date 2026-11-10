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
  the statement's Johnson threshold (`mem_candidates`, `thrOf_eq_johnsonThreshold`), and its
  execution, the capped halting run of its memory image, is valid
  (`Halting.candidateExecution_of_extracted`);
* the log has no collision, so its answers are injective (`answersInj_lookH`), and its support is
  finite, so the classically enumerated keys cover it (`keysCover_lookH`,
  `ExtractProofs.keysCover_supportKeys`);
* so the extractor, which decodes every candidate (`ExtractProofs.extract_of_candidate`), returns
  a valid execution.

`decodeStacks_length_le`: the stacks the list decoder returns are at most `2^12`.
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
theorem extractor_of_extracted {X : Type} (σ : Seeds X) {ℓ : Log} {k : ℕ} {π : Proof}
    (hf : ¬ Fail σ ℓ)
    (hv : Rom.verify (lookH ℓ) (lookF ℓ) (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π = some true)
    (hroot : ∀ r, announcedRoot prog π = some r → ∀ x, .inl (x, r) ∉ ℓ.drop k)
    (hx : Extracted prog input (cacheOf ℓ) π) :
    ∃ t, LeanVM.extractor prog input (cacheOf (ℓ.take k)) π = some t ∧
      ValidExecution prog input t := by
  obtain ⟨s₀, q₀, hx, hs₀, hM₀⟩ := hx
  unfold extractStack at hx
  dsimp only at hx
  split at hx
  · rename_i s ρ W hann hfw
    split at hx
    · rename_i hq
      obtain ⟨⟨root, ht, w, hroot', hW, st, haf, hhead⟩, hgood, level, rest, hcfg⟩ :=
        commitment_eq hv hann hfw
      obtain ⟨q, hqc, hM⟩ := hq
      obtain ⟨t, hct, -⟩ := Halting.candidateExecution_of_extracted hgood.2.1 hM
      have hadm := hgood.2.2.1
      simp only [stackLog_verifierLayout] at hadm hcfg
      have hcand := mem_candidates (A' := Extraction.johnsonThreshold (leanIsaμ prog s) ρ) hqc
        (thrOf_eq_johnsonThreshold hadm hcfg).ge
      have hWk : W = Extraction.committedWord (lookH (ℓ.take k)) root ht w :=
        hW.trans (committedWord_eq hf (hroot root hroot') ht w).symm
      rw [hWk] at hcand
      have hμ : 15 ≤ leanIsaμ prog s ∧ leanIsaμ prog s ≤ 32 := by
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

/-- **The extractor's list is short**: at every admissible shape, the stacks the list decoder
returns are distinct candidates of the word, so at most `2^12` (`spec_candidates_ncard_le`). -/
theorem decodeStacks_length_le {μ R : ℕ} (h : Whir.Admissible μ R) (W : ℕ → List K) :
    (Extraction.decodeStacks μ R W).length ≤ 2 ^ 12 := by
  have h1 := h.1
  have h2 := h.2.1
  unfold Whir.minLogStack at h1
  unfold Whir.maxLogStack at h2
  exact (Extraction.PruneProofs.length_decodeStacksAt_le (by show 6 ≤ μ; omega)
    (by show μ - 6 ≤ 64; omega) W).trans (spec_candidates_ncard_le h W)

/-- **The pruning keeps few prefixes**: at every admissible shape, after any `U ≥ 1` lanes at most
`2^12` prefixes survive. The survivors' encodings are distinct interleaved Reed–Solomon codewords
on `U` lanes, close to the word's first `U` lanes at the extractor's threshold
(`length_pruneUpTo_le`, `evalTuple_mem_code`), so the Johnson bound for the interleaved code on
`U` lanes caps them by level 0's `listMax` (`card_iList_johnsonAgreement_le_floor`), as
`spec_candidates_ncard_le` does for all `2^6` lanes. -/
theorem pruneUpTo_length_le {μ R : ℕ} (h : Whir.Admissible μ R) (W : ℕ → List K) {U : ℕ}
    (hU : 0 < U) :
    (Extraction.pruneUpTo (μ - LeanVM.Parameters.Whir.initialFold) R (Extraction.johnsonThreshold μ R) W U).length ≤
      2 ^ 12 := by
  classical
  obtain ⟨level, rest, hc⟩ := exists_ladder h
  obtain ⟨-, hμ, hκ, hR, hL, -, -⟩ := Whir.Params.deployed_spec_hyps h hc
  have hthr : (Whir.Params.deployedCodes μ R 0).thr = Extraction.johnsonThreshold μ R :=
    thrOf_eq_johnsonThreshold h hc
  set P := Whir.Params.deployedCodes μ R 0 with hP
  have hκ' : μ - LeanVM.Parameters.Whir.initialFold = P.κ := by rw [hκ]; rfl
  have hR' : R = P.R := hR.symm
  have hn64 : P.κ + P.R ≤ 64 := P.h64
  let O : Fin U → Fin P.n → K := fun u v ↦ Extraction.laneSymbol W u v
  let T := Whir.iList (ReedSolomon.code
    (Extraction.LaneProofs.domainEmb P.n (Nat.pow_le_pow_right (by norm_num) hn64)) (P.D + 1))
    P.thr O
  have hT : ∀ cs : List (Array K), cs.length = U → (∀ u < U, (cs.getD u #[]).size = 2 ^ P.κ) →
      P.thr ≤ (Extraction.PruneProofs.commonCols P.κ P.R W cs U).length →
        Extraction.PruneProofs.evalTuple P.κ P.R U cs ∈ T := by
    intro cs _ _ hA
    rw [Whir.mem_iList]
    refine ⟨fun u ↦ ?_, ?_⟩
    · rw [← P.two_pow_κ_eq]
      exact Extraction.PruneProofs.evalTuple_mem_code hn64 cs u
    · refine ⟨Finset.univ.filter fun v : Fin P.n ↦
          v.val ∈ Extraction.PruneProofs.commonCols P.κ P.R W cs U, ?_, ?_⟩
      · refine hA.trans (le_of_eq ?_)
        have hnd : (Extraction.PruneProofs.commonCols P.κ P.R W cs U).Nodup :=
          (List.nodup_range).filter _
        rw [← List.toFinset_card_of_nodup hnd]
        symm
        refine Finset.card_bij (fun v _ ↦ v.val) (fun v hv ↦ ?_)
          (fun a _ b _ h ↦ Fin.ext h) (fun b hb ↦ ?_)
        · simpa using (Finset.mem_filter.mp hv).2
        · have hb' := List.mem_toFinset.mp hb
          have hlt : b < P.n := by
            simp only [Extraction.PruneProofs.commonCols, List.mem_filter, List.mem_range] at hb'
            exact hb'.1
          exact ⟨⟨b, hlt⟩, by simpa using hb', rfl⟩
      · intro u v hv
        have hv' := (Finset.mem_filter.mp hv).2
        simp only [Extraction.PruneProofs.commonCols, List.mem_filter, List.mem_range,
          decide_eq_true_eq] at hv'
        exact (hv'.2 u u.isLt).symm
  calc _ ≤ T.card := by
        rw [← hthr, hκ', hR']
        exact Extraction.PruneProofs.length_pruneUpTo_le (by omega) W hU T hT
    _ ≤ P.listMax := Whir.card_iList_johnsonAgreement_le_floor _
        (by have := P.one_le_D; omega) (Nat.two_pow_pos _) P.hη O
    _ ≤ 2 ^ 12 := hL

end
end LeanVM.Protocol.EndToEnd.Sound
