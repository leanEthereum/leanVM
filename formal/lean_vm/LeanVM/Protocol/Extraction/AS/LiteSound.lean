/-
  LeanVM.Protocol.Extraction.AS.LiteSound

  The lite extractor returns every execution the leanVM knowledge extractor returns.
-/

module

public import LeanVM.Protocol.Extraction.AS.LiteEq
public import LeanVM.Protocol.Extraction.AS.Hash

/-!
# The lite extractor extracts what the extractor extracts

**`transcriptExtractorL_of`**: wherever `Relation.transcriptExtractor` returns an execution,
`transcriptExtractorL` returns it. Through the extractor over the skeleton
(`extractASF_of_extractAS`), then piece by piece:

* the seed, Keccak-256 through the transcript's first forward answers
  (`keccak256_of_lookupEvaluation`), and those answers indexed (`fwdF_fwdIndex`);
* the replays on values (`skelReplayP_eq`), the decoders on the sizes (`decSizesL_eq`,
  `decBodyL_eq`);
* the finish (`finishAS_eq_finishL`): the roots' words through one index of the transcript's
  evaluations (`leavesOf_eq`, `wordArrays_eq_wordsGo`), and the candidate on the sizes
  (`candidate_eq_candidateL`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.Whir.Params LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Relation LeanVM.Extraction.Fast Common

@[expose] public section

attribute [local instance] lexOrd

/-! ## The committed words -/

/-- **The committed leaves through the preimage index** are the statement's. -/
theorem leavesOf_eq (qs : List (PermutationQuery KeccakState × KeccakState)) (w h : ℕ)
    (root : Digest) :
    leavesOf qs w h root =
      let P := keccakEvaluationsOfTranscript qs
      committedLeaves (lookupEvaluation P) (P.map (·.1)) root h w := by
  unfold leavesOf committedLeaves
  rw [← subtreeLeavesWith_preimage]
  have key : ∀ d, ∀ len ∈ [64, 8 * w],
      preimageIn (transcriptIndex qs (max 64 (8 * w))) d len =
        preimage (answerPairs (lookupEvaluation (keccakEvaluationsOfTranscript qs))
          ((keccakEvaluationsOfTranscript qs).map (·.1))) d len := fun d len hlen ↦ by
    have hL : len ≤ max 64 (8 * w) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      omega
    rw [transcriptIndex, preimageIn_preimageIndex, answerPairs_firstAnswers,
      keccakEvaluationsFast_eq, ← filter_answerPairs, preimage_filter]
    intro p _ hp
    simp [hp, hL]
  exact subtreeLeavesWith_congr (fun d ↦ key d 64 (by simp)) (fun d ↦ key d (8 * w) (by simp)) h root

theorem le_capOf : ∀ (roots : List (Digest × ℕ × ℕ)) (x : Digest × ℕ × ℕ), x ∈ roots →
    max 64 (8 * x.2.2) ≤ capOf roots
  | [], _, h => absurd h List.not_mem_nil
  | y :: ys, x, h => by
    have h64 : 64 ≤ capOf ys := by
      cases ys with
      | nil => exact le_rfl
      | cons z zs => exact le_trans (le_max_left _ _) (le_capOf (z :: zs) z List.mem_cons_self)
    rcases List.mem_cons.1 h with rfl | h
    · simp only [capOf]; omega
    · have := le_capOf ys x h; simp only [capOf]; omega

theorem length_wordsGo (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits) :
    ∀ (i : ℕ) (roots : List (Digest × ℕ × ℕ)), (wordsGo μ R I i roots).length = roots.length
  | _, [] => rfl
  | i, _ :: xs => by simp [wordsGo, length_wordsGo μ R I (i + 1) xs]

theorem getElem_wordsGo (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits) :
    ∀ (i : ℕ) (roots : List (Digest × ℕ × ℕ)) (j : ℕ) (hj : j < roots.length),
      (wordsGo μ R I i roots)[j]'(by rw [length_wordsGo]; exact hj) =
        wordArrOf μ R I (i + j) roots[j]
  | _, [], _, hj => absurd hj (by simp)
  | i, x :: xs, 0, _ => rfl
  | i, x :: xs, j + 1, hj => by
    simp only [wordsGo, List.getElem_cons_succ]
    rw [getElem_wordsGo μ R I (i + 1) xs j (by simpa using hj)]
    congr 1
    omega

/-- **The words as arrays are the words through one index.** -/
theorem wordArrays_eq_wordsGo (μ R : ℕ) (qs : List (PermutationQuery KeccakState × KeccakState))
    (roots : List (Digest × ℕ × ℕ)) :
    wordArrays μ R (roots.map fun x ↦ (x.2.1, x.2.2,
        Extraction.committedWordC (lookupEvaluation (keccakEvaluationsOfTranscript qs))
          ((keccakEvaluationsOfTranscript qs).map (·.1)) x.1 x.2.1 x.2.2)) =
      wordsGo μ R (transcriptIndex qs (capOf roots)) 0 roots := by
  refine List.ext_getElem (by simp [wordArrays, length_wordsGo]) fun i h₁ h₂ ↦ ?_
  have hi : i < roots.length := by simpa [wordArrays] using h₁
  rw [getElem_wordsGo _ _ _ 0 roots i hi, Nat.zero_add]
  simp only [wordArrays, List.getElem_map, List.getElem_range]
  have hn : (codesOf μ R i).n = 2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) := by
    rw [lvC_eq]
  have hl : leavesAt (transcriptIndex qs (capOf roots)) roots[i] =
      leavesOf qs roots[i].2.2 roots[i].2.1 roots[i].1 :=
    leavesIn_transcriptIndex qs _ _ (le_capOf roots _ (List.getElem_mem hi)) _
  unfold wordArrOf laneRows laneRow
  rw [hl, leavesOf_eq]
  refine Array.ext (by simp [hn]) fun v hv₁ hv₂ ↦ ?_
  simp only [Array.getElem_ofFn]
  congr 2
  simp [wordOf, hi, Extraction.committedWordC]

/-! ## The candidate -/

theorem tables_stateLinks : (List.range nTables).map (fun t ↦
    let s := (tables.getD t default).links.stateLink
    (s.cycle, s.pc, s.fp)) =
      [(6, 0, 1), (8, 0, 1), (4, 0, 1), (9, 0, 1), (13, 0, 1), (67, 0, 1)] := by decide +kernel

theorem stateLink_of_lt {t : ℕ} (ht : t < nTables) :
    (tables.getD t default).links.stateLink.cycle = stateCyclesL.getD t 0 ∧
      (tables.getD t default).links.stateLink.pc = 0 ∧
      (tables.getD t default).links.stateLink.fp = 1 := by
  have h := congrArg (fun l ↦ l.getD t (0, 0, 0)) tables_stateLinks
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
    Option.map_some, Option.getD_some] at h
  have ht' : t < 6 := ht
  interval_cases t <;> simp_all [stateCyclesL]

theorem finalCycles_eq (layout : Layout) (hT : layout.tables = tables) {μ : ℕ} (q : Column μ)
    (chunks : Chunks) : finalCycles layout q chunks = finalCyclesL layout.lite q chunks := by
  unfold finalCycles finalCyclesL
  refine List.flatMap_congr fun t ht ↦ ?_
  obtain ⟨hc, hp, hf⟩ := stateLink_of_lt (List.mem_range.mp ht)
  simp only [tableAt, hT, hc, hp, hf, rowPtr, tableRowCount]
  rfl

/-- **The candidate on a layout of the deployed tables is the candidate on its sizes.** -/
theorem candidate_eq_candidateL (program : LeanIsaProgram) (layout : Layout)
    (hT : layout.tables = tables) {μ : ℕ} (q : Column μ) :
    candidate program layout q = candidateL program layout.lite q := by
  unfold candidate candidateL firstFinal firstFinalL
  have hc : linkChunks layout = chunksL layout.lite := rfl
  have hn : Link.linkCycles layout = layout.lite.tableRows.foldl (· + ·) 0 := rfl
  rw [hc, hn]
  rcases chunksL layout.lite with _ | chunks
  · rfl
  · simp only [finalCycles_eq layout hT]
    rfl

/-! ## The finish -/

theorem finishAS_eq_finishL (program : LeanIsaProgram)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (layout : Layout) (ρ : ℕ)
    (hT : layout.tables = tables) (tr : WhirTrace) (s : VerifierProgramState) :
    finishAS program (lookupEvaluation (keccakEvaluationsOfTranscript qs))
        ((keccakEvaluationsOfTranscript qs).map (·.1)) ((true, ((layout, ρ), tr)), s) =
      finishL program qs layout.lite ρ tr s.roots := by
  unfold finishAS finishL
  dsimp only
  rw [wordArrays_eq_wordsGo]
  refine congrArg _ (funext fun T ↦ ?_)
  split_ifs
  · rw [candidate_eq_candidateL program layout hT]
    rfl
  · rfl

/-! ## The extractor -/

theorem built_of_decSizes {bytecode : List K} {h : List Ev} {a : Layout × ℕ}
    (hd : decSizes bytecode h = some a) : a.1.tables = tables := by
  unfold decSizes at hd
  obtain ⟨ann, -, hs⟩ := Option.bind_eq_some_iff.mp hd
  unfold sizesOf at hs
  dsimp only at hs
  split_ifs at hs
  obtain ⟨layout, hl, hs⟩ := Option.bind_eq_some_iff.mp hs
  split_ifs at hs
  rw [Option.some.injEq] at hs
  subst hs
  exact (layoutBounds_of_buildLayout hl).tables_eq

/-- **Wherever the leanVM knowledge extractor returns an execution, the lite extractor returns
it.** -/
theorem transcriptExtractorL_of {prog : LeanIsaProgram} {input : PublicInput} {T : OracleQueryLog}
    {proof : Proof} {t : Execution prog}
    (h : Relation.transcriptExtractor prog input T proof = some t) :
    transcriptExtractorL prog input T proof = some t := by
  unfold Relation.transcriptExtractor transcriptExtractorWithHash at h
  have h' := extractASF_of_extractAS h
  unfold extractASF at h'
  obtain ⟨seed, hseed, h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain ⟨r₁, hr₁, h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain ⟨a, ha, h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain ⟨r₂, hr₂, h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain ⟨tr, htr, hfin⟩ := Option.bind_eq_some_iff.mp h'
  rw [seedRun_leanVmSeed] at hseed
  unfold seedWithHash fiatShamirIvWithHash at hseed
  obtain ⟨iv, hiv, hseed⟩ := Option.bind_eq_some_iff.mp hseed
  have hiv' := keccak256_of_lookupEvaluation hiv
  unfold transcriptExtractorL extractL
  simp only [fwdF_fwdIndex]
  have hs : seedWithHash (KeccakHash.keccak256With (Rpm.firstForward (permutationQueries T)))
      (Rpm.firstForward (permutationQueries T)) (bytecodeWords prog) (publicInputDigest input) =
        some seed := by
    unfold seedWithHash fiatShamirIvWithHash
    simp only [bind, Option.bind, hiv']
    exact hseed
  rw [hs, Option.bind_some, skelReplayP_eq, hr₁, Option.map_some, Option.bind_some,
    decSizesL_eq, ha, Option.map_some, Option.bind_some, skelReplayP_eq, hr₂, Option.map_some,
    Option.bind_some, ← decBodyL_eq, htr, Option.bind_some, ← hfin]
  exact (finishAS_eq_finishL prog _ a.1 a.2 (built_of_decSizes ha) tr r₂.2).symm

end
end LeanVM.Extraction.AS
