module

public import LeanVM.Protocol.Extraction.Fast.Lookup
public import LeanVM.Protocol.Extraction.Fast.Replay

/-!
# The transcript's preimage index

The transcript replayed through sorted maps (`SortedMap`), keeping the evaluations of at most
`L = max 64 (8·width)` bytes (`keccakEvaluationsFast`), their first answers and preimages indexed
(`firstAnswers`, `preimageIndex`): `transcriptIndex`, and a root's committed leaves read through it
(`leavesOf`).

* `preimage_filter`: `preimage pairs d len` reads only the pairs of `len` bytes;
* `filter_answerPairs`: the answered pairs of at most `L` bytes are those of the paths of at most
  `L` bytes;
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

/-- **A root's committed leaves**, its preimages read through the transcript's index of the
evaluations of at most `max 64 (8·w)` bytes. -/
@[expose] def leavesOf (qs : List (PermutationQuery KeccakState × KeccakState)) (w h : ℕ)
    (root : Digest) : Array (List K) :=
  subtreeLeavesWith (preimageIn (transcriptIndex qs (max 64 (8 * w)))) w h root

/-- A root's committed leaves, read through a preimage index `I`. -/
@[expose] def leavesIn (I : SortedMap (List UInt64 × ℕ) Hits) (w h : ℕ) (root : Digest) :
    Array (List K) :=
  subtreeLeavesWith (preimageIn I) w h root

/-- **An index of the evaluations of at most `L` bytes answers every lookup of at most `L' ≤ L`
bytes as the index at `L'` does**, so one index at the largest length serves every root. -/
theorem preimageIn_transcriptIndex_mono (T : List (PermutationQuery KeccakState × KeccakState))
    {L L' len : ℕ} (hL : L' ≤ L) (hlen : len ≤ L') (d : Digest) :
    preimageIn (transcriptIndex T L) d len = preimageIn (transcriptIndex T L') d len := by
  unfold transcriptIndex
  simp only [preimageIn_preimageIndex, answerPairs_firstAnswers]
  rw [keccakEvaluationsFast_eq, keccakEvaluationsFast_eq]
  generalize keccakEvaluationsOfTranscript T = E
  have hf : E.filter (fun e ↦ decide (e.1.length ≤ L')) =
      (E.filter fun e ↦ decide (e.1.length ≤ L)).filter fun e ↦ decide (e.1.length ≤ L') := by
    rw [List.filter_filter]
    refine List.filter_congr fun e _ ↦ ?_
    by_cases h : e.1.length ≤ L' <;> simp [h]; omega
  have ha := filter_answerPairs (E.filter fun e ↦ decide (e.1.length ≤ L)) L'
  simp only at ha
  rw [hf, ← ha, preimage_filter]
  intro p _ hp
  simp [hp, hlen]

/-- One index at a length at least a root's lookups' gives its leaves. -/
theorem leavesIn_transcriptIndex (T : List (PermutationQuery KeccakState × KeccakState)) {L : ℕ}
    (w h : ℕ) (hL : max 64 (8 * w) ≤ L) (root : Digest) :
    leavesIn (transcriptIndex T L) w h root = leavesOf T w h root :=
  subtreeLeavesWith_congr
    (fun d ↦ preimageIn_transcriptIndex_mono T hL (le_max_left _ _) d)
    (fun d ↦ preimageIn_transcriptIndex_mono T hL (le_max_right _ _) d) h root

end

end LeanVM.Extraction.Fast
