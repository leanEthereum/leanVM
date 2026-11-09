module

public import LeanVM.Protocol.Extraction.Fast.Lookup
public import LeanVM.Protocol.Extraction.Fast.Replay

/-!
# The extractor of the random-permutation model, fast

`transcriptExtractorFast` is `transcriptExtractor` (`Extraction/Extractor.lean`) with
every piece fast: the transcript replayed through sorted maps (`SortedMap`), keeping the evaluations of at most
`L = max 64 (8·width)` bytes (`keccakEvaluationsFast`), their first answers and preimages indexed
(`firstAnswers`, `preimageIndex`), and the decoder's Roth–Ruckenstein step a Taylor shift
(`extractWith`, on `decodeStacksFast`).

* `preimage_filter`: `preimage pairs d len` reads only the pairs of `len` bytes;
* `filter_answerPairs`: the answered pairs of at most `L` bytes are those of the paths of at most
  `L` bytes;
* **`transcriptExtractorFast_eq`**: `transcriptExtractorFast = transcriptExtractor`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Extraction LeanVM Common

public section

attribute [local instance] lexOrd

theorem hitsOf_filter (l : List (Bytes × Digest)) (f : Bytes × Digest → Bool)
    (k : List UInt64 × ℕ) (hf : ∀ p ∈ l, hitKey p = k → f p = true) :
    hitsOf (l.filter f) k = hitsOf l k := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have ih' := ih fun q hq ↦ hf q (List.mem_cons_of_mem _ hq)
    by_cases hp : f p = true
    · rw [List.filter_cons_of_pos hp, hitsOf, hitsOf, ih']
    · have hk : hitKey p ≠ k := fun h ↦ hp (hf p List.mem_cons_self h)
      rw [List.filter_cons_of_neg hp, ih', hitsOf]
      simp only [hk, ↓reduceIte, Hits.none_merge]

/-- `preimage pairs d len` reads only the pairs of `len` bytes. -/
theorem preimage_filter (pairs : List (Bytes × Digest)) (f : Bytes × Digest → Bool) (d : Digest)
    (len : ℕ) (hf : ∀ p ∈ pairs, p.1.length = len → f p = true) :
    preimage (pairs.filter f) d len = preimage pairs d len := by
  rw [preimage_eq_hitsOf, preimage_eq_hitsOf, hitsOf_filter]
  intro p hp hk
  exact hf p hp (by simp only [hitKey, Prod.mk.injEq] at hk; exact hk.2)

/-- The answered pairs of at most `L` bytes are those of the paths of at most `L` bytes. -/
theorem filter_answerPairs (P : List (Bytes × Digest)) (L : ℕ) :
    (answerPairs (lookupEvaluation P) (P.map (·.1))).filter (fun e ↦ decide (e.1.length ≤ L)) =
      let P' := P.filter fun e ↦ decide (e.1.length ≤ L)
      answerPairs (lookupEvaluation P') (P'.map (·.1)) := by
  have hk : (P.filter fun e ↦ decide (e.1.length ≤ L)).map (·.1) =
      (P.map (·.1)).filter fun x ↦ decide (x.length ≤ L) := by
    rw [List.filter_map]
    rfl
  simp only [answerPairs, List.filter_filterMap]
  rw [hk, List.filterMap_filter]
  refine List.filterMap_congr fun x _ ↦ ?_
  by_cases hx : x.length ≤ L
  · have hl : lookupEvaluation (P.filter fun e ↦ decide (e.1.length ≤ L)) x =
        lookupEvaluation P x := by
      simp only [lookupEvaluation, List.find?_filter]
      congr 1
      refine List.find?_congr fun p _ ↦ ?_
      by_cases hp : p.1 = x
      · simp [hp, hx]
      · simp [hp]
    simp only [hx, decide_true, ↓reduceIte, hl]
    cases lookupEvaluation P x <;> simp [Option.filter, hx]
  · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
    cases lookupEvaluation P x <;> simp [Option.filter, hx]

/-- The preimage index of the evaluations of at most `L` bytes a transcript holds. -/
@[expose] def transcriptIndex (T : List (PermutationQuery KeccakState × KeccakState)) (L : ℕ) :
    SortedMap (List UInt64 × ℕ) Hits :=
  let P := keccakEvaluationsFast T L
  preimageIndex (answerPairs (firstAnswers P).get? (P.map (·.1)))

/-- **The extractor in the random-permutation model, fast.** -/
@[expose] def transcriptExtractorFast (prog : LeanIsaProgram) (input : PublicInput) (T :
    OracleQueryLog)
    (proof : Proof) : Option (Execution prog) :=
  extractWith prog input (bytecodeWords prog)
    (fun width ↦ transcriptIndex (permutationQueries T) (max 64 (8 * width))) preimageIn proof

/-- **The fast extractor is the statement's.** -/
theorem transcriptExtractorFast_eq : transcriptExtractorFast = transcriptExtractor := by
  funext prog input T proof
  rw [transcriptExtractorFast, transcriptExtractor, ← extractFast_eq, ← extractWith_preimage]
  refine extractWith_congr _ _ _ _ _ _ _ (fun w d len hlen ↦ ?_) _
  have hL : len ≤ max 64 (8 * w) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    omega
  rw [transcriptIndex, preimageIn_preimageIndex, answerPairs_firstAnswers, keccakEvaluationsFast_eq,
    ← filter_answerPairs, preimage_filter]
  intro p _ hp
  simp [hp, hL]

end

end LeanVM.Extraction.Fast
